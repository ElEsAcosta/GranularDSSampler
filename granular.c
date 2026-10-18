// granular.c - sampler granular para tracks enteros en Nintendo DS/DSi (libnds + libfat, ARM9)
//
// Idea: la "cabeza de lectura" avanza sola por el track (play), y alrededor de ella se
// disparan granos. Velocidad y pitch son independientes: puedes estirar, congelar o
// invertir el track sin cambiar el tono (o al reves). Con DROP sueltas el track entero,
// limpio, sin ninguna modificacion, y puedes volver a la nube desde donde va la cancion.
//
// PANTALLA DE ABAJO (tactil): forma de onda en tiempo real
//   toca / arrastra la onda : scrub (suena aunque estes en pausa; si estabas en DROP, lo suelta)
//   botones: [play/pausa] [loop] [al inicio] [carpeta = cargar WAV] [DROP]
//   linea amarilla = cabeza de lectura (cian en DROP), onda azul = ya reproducido,
//   fondo verde = region de loop, fondo claro = spray, onda blanca = ancho de un grano,
//   marcas naranjas = granos sonando
//
// BOTONES
//   START       play / pausa
//   A           DROP: fundido hacia el track limpio; otra vez A vuelve a la nube (retoma donde va la cancion)
//   B (mantener) freeze: congela la cabeza, sigue sonando la nube de granos
//   SELECT      loop on/off
//   X / Y       fijar inicio / fin del loop en la posicion actual (Y activa el loop)
//   L / R       saltar -5 s / +5 s (en DROP salta el track limpio)
//   Arr / Abajo elegir parametro, Izq / Der cambiar su valor
//
// PARAMETROS (menu de arriba, con scroll)
//   VELOCID -200..+200 %   (0 = congelado, negativo = hacia atras, sin cambiar el pitch)
//   PITCH -24..+24 st   TAMANO 10..2000 ms   DENSID 1..100 granos/s
//   SPRAY 0..500 ms (aleatoriedad de posicion)   DERIVA 0..100 (la posicion divaga lentamente)
//   ARMONIA 0..100 % de granos transpuestos a -12/-5/+7/+12 (efecto shimmer / pad)
//   JITTER 0..100 cents   REVERSA 0..100 % de granos al reves
//   REVERB 0..100 % mezcla   COLA 0..100 (largo de la cola, hasta ~10 s)
//   VOLUMEN (1.0x = el track limpio sale tal cual)   FUNDIDO 0.05..16 s (duracion del DROP)
//   DROP DE inicio / la cabeza (desde donde arranca el track limpio)
//   CARGAR  abre la SD (tambien: boton de carpeta)   MIC REC  graba 2 s del microfono
//
// El volumen de la nube se compensa solo segun cuantos granos se solapan (densidad x tamano),
// asi un pad grueso no suena mas fuerte que uno disperso.
//
// WAV soportados: PCM 8/16/24 bit, mono o estereo, cualquier frecuencia. Se mezcla a mono,
// se normaliza y se guarda en 8 bit; si no cabe en RAM (la DS tiene 4 MB) se reduce la
// frecuencia de muestreo. La primera carga de cada WAV crea "<archivo>.wav.gr8" en la SD
// (version liviana); las siguientes cargas son casi instantaneas.
// MP3 y otros formatos: convertirlos antes en el PC con to_ds.py.

#include <nds.h>
#include <fat.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <dirent.h>
#include <unistd.h>
#include <math.h>

#define OUT_RATE    32768   // lo que pedimos; el hardware corre a ~32728.5 Hz
#define OUT_LEN     4096    // anillo de salida: 4096 muestras = 1 vuelta del timer (DIV_64)
#define CHUNK       256     // muestras que renderizamos por tanda
#define LEAD        1536    // cuanto renderizamos por delante del playhead (~47 ms)
#define MAX_GRAINS  16
#define WIN_LEN     256

#define REC_RATE    16000   // frecuencia del mic
#define REC_LEN     (REC_RATE * 2)

#define MAX_SECS    180     // limite: 3 minutos
#define BUDGET      2900000 // bytes de RAM para el sample (8 bit)

#define MIX_FULL    (1 << 24)   // mezcla del DROP en Q24: 0 = solo nube, MIX_FULL = solo track limpio

// posicion del grano = indice entero (u32) + fraccion de 16 bit; el indice necesita mas de
// 16 bit porque un track de 3 min tiene millones de muestras
typedef struct { u32 ipos; s32 fpos; s32 inc; u32 wpos, winc; bool on; } Grain;

static Grain grains[MAX_GRAINS];
static s16 out[OUT_LEN] __attribute__((aligned(32)));
static u8  mic[REC_LEN] __attribute__((aligned(32)));
static s8  recBuf[REC_LEN];          // sample inicial / grabacion del mic
static s16 win[WIN_LEN + 1];         // +1 para interpolar la ventana

static s8  *src = recBuf, *heapBuf = NULL;   // sample activo (s8)
static u32 srcLen = REC_LEN, srcRate = REC_RATE;
static char curName[128] = "[demo]";
static bool lostSample = false;      // true si una carga fallida nos dejo sin el sample anterior

// transporte de la nube
static s32  posI = 0, posF = 0;      // cabeza de lectura: indice + fraccion (16 bit)
static bool playing = false, touching = false, freezeKey = false, loopOn = false;
static s32  loopStart = 0, loopEnd = REC_LEN - 1;

// DROP: voz de reproduccion limpia
static bool dropOn = false, dropFromHead = false;
static s32  mixQ = 0;                // 0 = solo nube ... MIX_FULL = solo track limpio
static s32  trackI = 0, trackF = 0;  // posicion de la voz limpia
static s32  trackGate = 0;           // compuerta Q15 (evita clicks al pausar)
static s32  fadeIdx = 4;
static const float fadeSec[8] = { 0.05f, 0.25f, 0.5f, 1.0f, 2.0f, 4.0f, 8.0f, 16.0f };
static const char *const fadeTxt[8] = { "0.05 s", "0.25 s", "0.5 s", "1 s", "2 s", "4 s", "8 s", "16 s" };

// parametros
static s32 speedPct = 100, semis = 0, sizeMs = 120, density = 24, sprayMs = 30;
static s32 driftPct = 0, harmPct = 0, jitterC = 0, revPct = 0;
static s32 revMixPct = 20, decayPct = 60;
static s32 gain = 40;                // volumen de la nube, Q4; el track limpio usa gain*2/5 (40 = 1.0x)
static u32 inc16;                    // pitch: incremento de lectura de un grano (16.16)
static u32 cleanInc;                 // lectura 1x del track limpio (16.16)
static s32 scanInc;                  // velocidad: avance de la cabeza por muestra de salida (16.16, con signo)
static s32 normQ = 256;              // compensacion por solapamiento de granos (Q8)
static s32 fadeStep = 1000;          // avance de mixQ por muestra
static s32 harmRatio[4];             // razones Q16 de -12, -5, +7, +12 semitonos
static s32 driftW = 0;               // caminata aleatoria de la posicion

static u32 rng = 2463534242u;
static s32 untilSpawn = 1;
static volatile bool micDone = false;
static bool recording = false, sdOK = false;
static bool browsing = false, touchDrag = false;     // navegador de la SD abierto / arrastre en la onda

static PrintConsole top;
static u16 *fb;                       // pantalla de abajo: bitmap de 16 bit
static u8 waveA[256], waveB[256];     // por columna: fila superior / inferior de la onda
static bool fullRedraw = true;

static void computePeaks(void);       // definida mas abajo (vista)

static u32 rnd(void) { rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5; return rng; }
static s32 clampi(s32 v, s32 lo, s32 hi) { return v < lo ? lo : (v > hi ? hi : v); }
static s32 clamp16(s32 v) { return v > 32767 ? 32767 : (v < -32768 ? -32768 : v); }

static u16 rd16(const u8 *p) { return (u16)(p[0] | (p[1] << 8)); }
static u32 rd32(const u8 *p) { return (u32)p[0] | ((u32)p[1] << 8) | ((u32)p[2] << 16) | ((u32)p[3] << 24); }

// ---------------------------------------------------------------- reverb (Schroeder: 4 combs + 2 allpass)
typedef struct { s16 *buf; u32 len, idx; s32 lp; } Comb;
static s16 cb0[1789], cb1[1999], cb2[2237], cb3[2459], ab0[557], ab1[421];
static Comb combs[4] = { { cb0, 1789, 0, 0 }, { cb1, 1999, 0, 0 }, { cb2, 2237, 0, 0 }, { cb3, 2459, 0, 0 } };
static Comb aps[2]   = { { ab0, 557, 0, 0 }, { ab1, 421, 0, 0 } };
static s32 revMix = 51, revFb = 220, revDamp = 80;      // Q8

static void updateReverb(void) {
    revMix = revMixPct * 256 / 100;
    revFb  = 179 + decayPct * 69 / 100;                  // 0.70 .. 0.97
}

static s32 reverbProcess(s32 in) {
    s32 x = (in * (256 - revFb)) >> 8;                   // compensa la ganancia de la realimentacion
    s32 sum = 0;
    for (int i = 0; i < 4; i++) {
        Comb *c = &combs[i];
        s32 y = c->buf[c->idx];
        c->lp += ((y - c->lp) * revDamp) >> 8;           // amortiguacion: la cola se oscurece
        c->buf[c->idx] = (s16)clamp16(x + ((c->lp * revFb) >> 8));
        if (++c->idx >= c->len) c->idx = 0;
        sum += y;
    }
    s32 w = sum >> 2;
    for (int i = 0; i < 2; i++) {                        // difusion
        Comb *a = &aps[i];
        s32 z = a->buf[a->idx];
        s32 v = clamp16(w + (z >> 1));
        a->buf[a->idx] = (s16)v;
        if (++a->idx >= a->len) a->idx = 0;
        w = z - (v >> 1);
    }
    return w;
}

// ---------------------------------------------------------------- motor
static void updateInc(void) {
    float base = (float)srcRate / 32728.5f;                    // frecuencia del sample -> salida
    inc16    = (u32)(65536.0f * base * exp2f(semis / 12.0f));
    cleanInc = (u32)(65536.0f * base);
    scanInc  = (s32)(65536.0f * base * (speedPct / 100.0f));
    float ov = (float)density * (float)sizeMs / 1000.0f;       // granos solapados en promedio
    normQ    = (s32)(256.0f / sqrtf(ov < 1.0f ? 1.0f : ov));
    fadeStep = (s32)((float)MIX_FULL / (fadeSec[fadeIdx] * 32728.5f));
    if (fadeStep < 1) fadeStep = 1;
}

static void killGrains(void) {
    for (int g = 0; g < MAX_GRAINS; g++) grains[g].on = false;
    untilSpawn = 1;
}

static s32 minLoop(void) { s32 m = (s32)(srcLen / 4); return m > 2000 ? 2000 : m; }

static void resetTransport(bool autoplay, bool loop) {
    posI = 0; posF = 0;
    loopStart = 0; loopEnd = (s32)srcLen - 1;
    loopOn = loop;
    playing = autoplay;
    dropOn = false; mixQ = 0; trackI = 0; trackF = 0; driftW = 0;
    killGrains();
}

static s32 curPos(void) { return dropOn ? trackI : posI; }

static void seekTo(s32 idx) {
    posI = clampi(idx, 0, (s32)srcLen - 1);
    posF = 0;
}

static void seekRel(s32 delta) {
    if (dropOn) { trackI = clampi(trackI + delta, 0, (s32)srcLen - 2); trackF = 0; }
    else        seekTo(posI + delta);
}

static void togglePlay(void) {
    if (!playing) {
        if (!dropOn && !loopOn && posI >= (s32)srcLen - 2) seekTo(0);   // estaba al final: vuelve a empezar
        playing = true;
    } else {
        playing = false;
    }
}

// DROP: fundido hacia el track limpio. Otra vez: fundido de vuelta a la nube, que retoma donde va la cancion.
static void toggleDrop(void) {
    if (!dropOn) {
        if (dropFromHead) { trackI = posI; trackF = posF; }
        else              { trackI = 0;    trackF = 0; }
        trackI = clampi(trackI, 0, (s32)srcLen - 2);
        dropOn = true;
        playing = true;
    } else {
        dropOn = false;
        posI = clampi(trackI, 0, (s32)srcLen - 1);
        posF = trackF;
        untilSpawn = 1;
    }
}

static void fixLoop(bool movedStart) {
    if (loopStart < 0) loopStart = 0;
    if (loopEnd > (s32)srcLen - 1) loopEnd = (s32)srcLen - 1;
    s32 m = minLoop();
    if (loopEnd - loopStart < m) {
        if (movedStart) {
            loopEnd = loopStart + m;
            if (loopEnd > (s32)srcLen - 1) { loopEnd = (s32)srcLen - 1; loopStart = loopEnd - m; }
        } else {
            loopStart = loopEnd - m;
            if (loopStart < 0) { loopStart = 0; loopEnd = m; }
        }
    }
}

static void toggleLoop(void) {
    if (!loopOn && loopEnd - loopStart < minLoop()) { loopStart = 0; loopEnd = (s32)srcLen - 1; }
    loopOn = !loopOn;
}

// avanza la cabeza una muestra de salida
static inline void advancePos(void) {
    posF += scanInc;
    posI += posF >> 16;
    posF &= 0xFFFF;
    if (loopOn) {
        if (scanInc > 0 && posI >= loopEnd) {
            posI = loopStart + (posI - loopEnd);
            if (posI >= loopEnd) posI = loopStart;
        } else if (scanInc < 0 && posI < loopStart) {
            posI = loopEnd - (loopStart - posI);
            if (posI < loopStart) posI = loopEnd - 1;
        }
    } else if (posI >= (s32)srcLen - 1) {
        posI = (s32)srcLen - 1; posF = 0; playing = false;      // fin del track
    } else if (posI < 0) {
        posI = 0; posF = 0; playing = false;
    }
}

static void spawn(void) {
    for (int g = 0; g < MAX_GRAINS; g++) {
        if (grains[g].on) continue;
        s32 sp = (s32)(sprayMs * srcRate / 1000);
        s32 start = posI + (s32)(rnd() % (u32)(2 * sp + 1)) - sp;
        if (driftPct) {                                           // deriva: caminata aleatoria con retorno suave
            s32 step = (s32)(driftPct * srcRate / 1000);
            driftW += (s32)(rnd() % (u32)(2 * step + 1)) - step;
            driftW -= driftW / 32;
            start += driftW;
        }
        s32 inc = (s32)inc16;
        if (harmPct && (rnd() % 100) < (u32)harmPct)              // armonia: grano transpuesto
            inc = (s32)(((u64)(u32)inc * (u32)harmRatio[rnd() & 3]) >> 16);
        if (jitterC) {                                            // desafinacion aleatoria en cents
            s32 j = (s32)(rnd() % (u32)(2 * jitterC + 1)) - jitterC;
            inc += (inc * j) / 1731;
        }
        u32 len = (u32)(sizeMs * OUT_RATE / 1000);
        if (revPct && (rnd() % 100) < (u32)revPct) {              // grano al reves: parte del final
            start += (s32)(((len >> 4) * ((u32)inc >> 4)) >> 8);
            inc = -inc;
        }
        start = clampi(start, 0, (s32)srcLen - 2);
        grains[g].ipos = (u32)start;
        grains[g].fpos = 0;
        grains[g].inc  = inc;
        grains[g].wpos = 0;
        grains[g].winc = ((u32)WIN_LEN << 16) / len;
        grains[g].on   = true;
        return;
    }
}

// limitador suave: lineal hasta 16384 y luego comprime hacia 32767 (sin clipping duro)
static s32 softClip(s32 x) {
    s32 a = x < 0 ? -x : x;
    if (a > 16384) {
        s32 d = a - 16384;
        if (d > 65535) d = 65535;
        a = 16384 + (d * 16383) / (d + 16383);
    }
    return x < 0 ? -a : a;
}

// todo en enteros: el ARM9 no tiene FPU
static void render(s16 *dst, int n) {
    for (int i = 0; i < n; i++) {
        if (recording) { dst[i] = 0; continue; }

        // fundido nube <-> track limpio
        if (dropOn) {
            if (mixQ < MIX_FULL) {
                mixQ += fadeStep;
                if (mixQ >= MIX_FULL) { mixQ = MIX_FULL; killGrains(); }   // la nube ya no se oye: no gasta CPU
            }
        } else if (mixQ > 0) {
            mixQ -= fadeStep;
            if (mixQ < 0) mixQ = 0;
        }

        // nube de granos
        s32 c = 0;
        if (mixQ < MIX_FULL) {
            if (playing && !touching && !freezeKey) advancePos();
            if (playing || touching) {
                if (--untilSpawn <= 0) { spawn(); untilSpawn = OUT_RATE / density; }
            }
            s32 acc = 0;
            for (int g = 0; g < MAX_GRAINS; g++) {
                Grain *gr = &grains[g];
                if (!gr->on) continue;
                u32 si = gr->ipos;
                if (si >= srcLen - 1 || gr->wpos >= ((u32)WIN_LEN << 16)) { gr->on = false; continue; }
                s32 a = src[si], b = src[si + 1];
                s32 s = a + (((b - a) * (gr->fpos >> 8)) >> 8);        // interpolacion lineal
                u32 wi = gr->wpos >> 16;
                s32 w = win[wi] + (((win[wi + 1] - win[wi]) * (s32)((gr->wpos >> 8) & 0xFF)) >> 8);
                acc += (s * w) >> 7;                                    // s8 -> s16 con ventana Q15
                s32 f = gr->fpos + gr->inc;
                gr->ipos += (u32)(f >> 16);
                gr->fpos  = f & 0xFFFF;
                gr->wpos += gr->winc;
            }
            c = softClip((((acc * normQ) >> 8) * gain) >> 4);
        }

        // reverb sobre la nube; el fundido la apaga junto con ella
        s32 rv = reverbProcess(c);
        s32 cm = (c * (256 - (revMix >> 1)) + rv * revMix) >> 8;
        cm = (cm * (32768 - (mixQ >> 9))) >> 15;

        // voz limpia: el track tal cual, 1x, sin pitch, sin granos, sin limitador
        s32 tr = 0;
        if (dropOn || mixQ > 0) {
            if (playing) { trackGate += 50; if (trackGate > 32768) trackGate = 32768; }
            else if (trackGate > 0) { trackGate -= 50; if (trackGate < 0) trackGate = 0; }
            if (playing || trackGate > 0) {
                u32 ti = (u32)trackI;
                if (ti >= srcLen - 1) {                                 // fin de la cancion
                    dropOn = false; posI = (s32)srcLen - 1; posF = 0; playing = false;
                } else {
                    s32 a = src[ti], b = src[ti + 1];
                    s32 s = a + (((b - a) * (trackF >> 8)) >> 8);
                    s32 x = (((s << 8) * ((gain * 2) / 5)) >> 4);
                    tr = (x * (trackGate >> 3)) >> 12;
                    trackF += (s32)cleanInc;
                    trackI += trackF >> 16;
                    trackF &= 0xFFFF;
                }
            }
        }
        dst[i] = (s16)clamp16(cm + tr);
    }
}

// ---------------------------------------------------------------- sample
static void freeHeap(void) { if (heapBuf) { free(heapBuf); heapBuf = NULL; } }

static void resetSrc(void) {
    freeHeap();
    src = recBuf; srcLen = REC_LEN; srcRate = REC_RATE;
    lostSample = true;
}

static void useRec(const char *name) {
    freeHeap();
    src = recBuf; srcLen = REC_LEN; srcRate = REC_RATE;
    lostSample = false;
    strncpy(curName, name, sizeof(curName) - 1);
    updateInc();
    resetTransport(true, true);                  // demo / mic: suena en loop de inmediato
    computePeaks();
}

// ---------------------------------------------------------------- microfono
static void micCb(void *buf, int len) { (void)buf; (void)len; micDone = true; }

static void startRec(void) {
    killGrains();
    playing = false;
    dropOn = false; mixQ = 0;
    recording = true;
    micDone = false;
    soundMicRecord(mic, REC_LEN, MicFormat_8Bit, REC_RATE, micCb);
}

static void finishRec(void) {
    soundMicOff();
    DC_InvalidateRange(mic, REC_LEN);
    int peak = 4;
    for (int i = 0; i < REC_LEN; i++) {
        int v = (int)mic[i] - 128;           // el mic entrega 8 bit sin signo
        if (v < 0) v = -v;
        if (v > peak) peak = v;
    }
    for (int i = 0; i < REC_LEN; i++) {
        int v = ((int)mic[i] - 128) * 127 / peak;   // normaliza
        if (v > 127) v = 127;
        if (v < -127) v = -127;
        recBuf[i] = (s8)v;
    }
    recording = false;
    useRec("[mic]");
}

// ---------------------------------------------------------------- WAV + cache
static void wr32(u8 *p, u32 v) { p[0] = (u8)v; p[1] = (u8)(v >> 8); p[2] = (u8)(v >> 16); p[3] = (u8)(v >> 24); }

// Cache: "<archivo>.wav.gr8" = cabecera de 16 bytes ('G','R','8',2, tamano del wav,
// frecuencia, largo) + muestras s8 ya normalizadas. Si el WAV cambia de tamano, se regenera.
static bool loadCache(const char *name, u32 wavSize) {
    char cn[160];
    snprintf(cn, sizeof(cn), "%s.gr8", name);
    FILE *f = fopen(cn, "rb");
    if (!f) return false;
    u8 h[16];
    if (fread(h, 1, 16, f) != 16 || h[0] != 'G' || h[1] != 'R' || h[2] != '8' || h[3] != 2 ||
        rd32(h + 4) != wavSize) { fclose(f); return false; }
    u32 rate = rd32(h + 8), len = rd32(h + 12);
    if (rate < 1000 || rate > 48000 || len < 256 || len > 3000000) { fclose(f); return false; }
    resetSrc();
    s8 *buf = (s8 *)malloc(len);
    if (!buf) { fclose(f); return false; }
    size_t got = fread(buf, 1, len, f);
    fclose(f);
    if (got != len) { free(buf); return false; }
    heapBuf = buf; src = buf; srcLen = len; srcRate = rate;
    lostSample = false;
    strncpy(curName, name, sizeof(curName) - 1);
    updateInc();
    resetTransport(false, false);                // los tracks cargan en pausa, al inicio
    computePeaks();
    return true;
}

static void saveCache(const char *name, u32 wavSize, const s8 *buf, u32 len, u32 rate) {
    char cn[160];
    snprintf(cn, sizeof(cn), "%s.gr8", name);
    FILE *f = fopen(cn, "wb");
    if (!f) return;                                   // SD protegida o sin permisos: no pasa nada
    u8 h[16] = { 'G', 'R', '8', 2 };
    wr32(h + 4, wavSize); wr32(h + 8, rate); wr32(h + 12, len);
    bool ok = (fwrite(h, 1, 16, f) == 16);
    for (u32 o = 0; ok && o < len; ) {
        u32 n = len - o;
        if (n > 16384) n = 16384;
        ok = (fwrite(buf + o, 1, n, f) == n);
        o += n;
    }
    fclose(f);
    if (!ok) remove(cn);
}

// devuelve NULL si todo bien, o un mensaje de error
static const char *loadWav(const char *name) {
    FILE *f = fopen(name, "rb");
    if (!f) return "no se pudo abrir";

    fseek(f, 0, SEEK_END);
    u32 wavSize = (u32)ftell(f);
    fseek(f, 0, SEEK_SET);
    if (loadCache(name, wavSize)) { fclose(f); return NULL; }   // ya convertido antes

    u8 h[12];
    if (fread(h, 1, 12, f) != 12 || memcmp(h, "RIFF", 4) || memcmp(h + 8, "WAVE", 4)) {
        fclose(f); return "no es un WAV";
    }

    u16 fmt = 0, ch = 0, bits = 0;
    u32 rate = 0, dataLen = 0;
    bool haveFmt = false, haveData = false;
    u8 c[8];
    while (fread(c, 1, 8, f) == 8) {
        u32 sz = rd32(c + 4);
        if (!memcmp(c, "fmt ", 4)) {
            u8 b[16];
            if (sz < 16 || fread(b, 1, 16, f) != 16) { fclose(f); return "fmt invalido"; }
            fmt = rd16(b); ch = rd16(b + 2); rate = rd32(b + 4); bits = rd16(b + 14);
            haveFmt = true;
            fseek(f, (long)(sz - 16 + (sz & 1)), SEEK_CUR);
        } else if (!memcmp(c, "data", 4)) {
            dataLen = sz; haveData = true; break;
        } else {
            fseek(f, (long)(sz + (sz & 1)), SEEK_CUR);
        }
    }
    if (!haveFmt || !haveData) { fclose(f); return "WAV incompleto"; }
    if ((fmt != 1 && fmt != 0xFFFE) || (ch != 1 && ch != 2) ||
        (bits != 8 && bits != 16 && bits != 24) || rate == 0) {
        fclose(f); return "solo PCM 8/16/24 mono/estereo";
    }

    long pos = ftell(f);
    fseek(f, 0, SEEK_END);
    long end = ftell(f);
    fseek(f, pos, SEEK_SET);
    if ((long)dataLen > end - pos) dataLen = (u32)(end - pos);   // WAV en streaming o truncado

    u32 blockAlign = (u32)ch * (bits / 8);
    u32 frames = dataLen / blockAlign;
    if (frames > (u32)MAX_SECS * rate) frames = (u32)MAX_SECS * rate;   // max 3 min
    if (frames < 256) { fclose(f); return "archivo muy corto"; }

    // liberamos el sample anterior antes de pedir RAM; si falla volvemos al demo
    resetSrc();

    u32 budget = BUDGET, storeRate, outLen;
    s8 *buf = NULL;
    while (1) {
        storeRate = rate;
        if (storeRate > 32728) storeRate = 32728;
        if ((u64)frames * storeRate / rate > budget)
            storeRate = (u32)((u64)budget * rate / frames);
        if (storeRate < 4000) storeRate = 4000;
        outLen = (u32)((u64)frames * storeRate / rate);
        buf = (s8 *)malloc(outLen);
        if (buf) break;
        budget = budget * 3 / 4;
        if (budget < 200000) { fclose(f); return "sin memoria"; }
    }

    u8 *blk = (u8 *)malloc(4096);
    if (!blk) { free(buf); fclose(f); return "sin memoria"; }
    u32 perBlk = 4096 / blockAlign;

    u32 j = 0, done = 0, phase = 0, cnt = 0, nb = 0;
    s32 acc = 0;
    int pk = 0;                                             // pico del sample (para normalizar)
    while (done < frames) {
        u32 n = frames - done;
        if (n > perBlk) n = perBlk;
        if (fread(blk, blockAlign, n, f) != n) break;
        for (u32 k = 0; k < n; k++) {
            const u8 *p = blk + k * blockAlign;
            s32 m;
            if (bits == 16) {
                m = (s16)rd16(p);
                if (ch == 2) m = (m + (s16)rd16(p + 2)) >> 1;
            } else if (bits == 8) {
                m = ((s32)p[0] - 128) << 8;
                if (ch == 2) m = (m + (((s32)p[1] - 128) << 8)) >> 1;
            } else {
                m = (s16)rd16(p + 1);                       // 24 bit: nos quedamos con los 16 altos
                if (ch == 2) m = (m + (s16)rd16(p + 4)) >> 1;
            }
            acc += m; cnt++;
            phase += storeRate;
            if (phase >= rate) {                            // decimacion con promedio (anti-alias basico)
                phase -= rate;
                if (j < outLen) {
                    s8 v = (s8)((acc / (s32)cnt) >> 8);
                    int av = v < 0 ? -v : v;
                    if (av > pk) pk = av;
                    buf[j++] = v;
                }
                acc = 0; cnt = 0;
            }
        }
        done += n;
        if ((++nb & 31) == 0) iprintf("\x1b[12;0H  %3lu%%", (unsigned long)(done / (frames / 100 + 1)));
    }
    free(blk);
    fclose(f);

    if (j < 256) { free(buf); return "error leyendo la SD"; }

    if (pk > 0 && pk < 110) {                               // normaliza: sube samples bajitos hasta ~127
        s32 mul = (127 << 8) / pk;
        for (u32 i = 0; i < j; i++) {
            s32 v = ((s32)buf[i] * mul) >> 8;
            if (v > 127) v = 127;
            if (v < -127) v = -127;
            buf[i] = (s8)v;
        }
    }

    heapBuf = buf; src = buf; srcLen = j; srcRate = storeRate;
    lostSample = false;
    strncpy(curName, name, sizeof(curName) - 1);
    updateInc();
    resetTransport(false, false);                           // los tracks cargan en pausa, al inicio
    computePeaks();

    iprintf("\x1b[14;0H  guardando cache...   ");
    saveCache(name, wavSize, buf, j, storeRate);
    return NULL;
}

// ---------------------------------------------------------------- navegador
#define MAX_ENT 128
typedef struct { char name[128]; u8 dir; } Ent;
static Ent ents[MAX_ENT];
static int nEnt = 0, sel = 0, scrollTop = 0;

static int entCmp(const void *a, const void *b) {
    const Ent *x = (const Ent *)a, *y = (const Ent *)b;
    if (x->dir != y->dir) return (int)y->dir - (int)x->dir;   // carpetas primero
    return strcasecmp(x->name, y->name);
}

static void scanDir(void) {
    nEnt = 0; sel = 0; scrollTop = 0;
    DIR *d = opendir(".");
    if (!d) return;
    struct dirent *e;
    while ((e = readdir(d)) && nEnt < MAX_ENT) {
        if (!strcmp(e->d_name, ".")) continue;
        bool dir = (e->d_type == DT_DIR);
        if (!dir) {
            size_t n = strlen(e->d_name);
            if (n < 5 || strcasecmp(e->d_name + n - 4, ".wav")) continue;
        }
        strncpy(ents[nEnt].name, e->d_name, sizeof(ents[nEnt].name) - 1);
        ents[nEnt].name[sizeof(ents[nEnt].name) - 1] = 0;
        ents[nEnt].dir = dir;
        nEnt++;
    }
    closedir(d);
    qsort(ents, nEnt, sizeof(Ent), entCmp);
}

static void drawBrowser(void) {
    consoleSelect(&top);
    iprintf("\x1b[2J");
    char cwd[256];
    if (!getcwd(cwd, sizeof(cwd))) strcpy(cwd, "?");
    iprintf("SD %.28s\n\n", cwd);
    if (nEnt == 0) iprintf("  (sin .wav ni carpetas)\n");
    for (int r = 0; r < 19; r++) {
        int i = scrollTop + r;
        if (i >= nEnt) break;
        iprintf("%c %s%.27s%s\n", i == sel ? '>' : ' ',
                ents[i].dir ? "[" : "", ents[i].name, ents[i].dir ? "]" : "");
    }
    iprintf("\x1b[23;0HA abrir  B cancelar");
}

// abre el navegador de la SD (desde el menu o el boton de carpeta)
static void openBrowser(void) {
    if (!sdOK) return;
    touching = false; touchDrag = false; freezeKey = false;
    scanDir();
    browsing = true;
    drawBrowser();
}

// ---------------------------------------------------------------- parametros / texto
enum { P_SPEED, P_PITCH, P_SIZE, P_DENS, P_SPRAY, P_DRIFT, P_HARM, P_JIT, P_REV,
       P_REVERB, P_DECAY, P_VOL, P_FADE, P_DROPFROM, P_LOAD, P_REC, P_COUNT };
static const char *const pLabel[P_COUNT] = {
    "VELOCID", "PITCH", "TAMANO", "DENSID", "SPRAY", "DERIVA", "ARMONIA", "JITTER", "REVERSA",
    "REVERB", "COLA", "VOLUMEN", "FUNDIDO", "DROP DE", "CARGAR", "MIC REC"
};
static int cur = 0, pTop = 0;
#define P_ROWS 13

static s32 stepSize(s32 v) { return v < 100 ? 10 : (v < 500 ? 50 : 100); }

static void adjust(int d) {
    switch (cur) {
        case P_SPEED: speedPct = clampi(speedPct + d * 5, -200, 200); updateInc(); break;
        case P_PITCH: semis    = clampi(semis + d, -24, 24);          updateInc(); break;
        case P_SIZE:  sizeMs   = clampi(sizeMs + d * stepSize(d > 0 ? sizeMs : sizeMs - 1), 10, 2000); updateInc(); break;
        case P_DENS:  density  = clampi(density + d * ((d > 0 ? density : density - 1) < 10 ? 1 : 2), 1, 100); updateInc(); break;
        case P_SPRAY: sprayMs  = clampi(sprayMs + d * 10, 0, 500);    break;
        case P_DRIFT: driftPct = clampi(driftPct + d * 5, 0, 100);    if (!driftPct) driftW = 0; break;
        case P_HARM:  harmPct  = clampi(harmPct + d * 5, 0, 100);     break;
        case P_JIT:   jitterC  = clampi(jitterC + d * 5, 0, 100);     break;
        case P_REV:   revPct   = clampi(revPct + d * 10, 0, 100);     break;
        case P_REVERB: revMixPct = clampi(revMixPct + d * 5, 0, 100); updateReverb(); break;
        case P_DECAY: decayPct = clampi(decayPct + d * 5, 0, 100);    updateReverb(); break;
        case P_VOL:   gain     = clampi(gain + d * 4, 4, 128);        break;
        case P_FADE:  fadeIdx  = clampi(fadeIdx + d, 0, 7);           updateInc(); break;
        case P_DROPFROM: dropFromHead = !dropFromHead;                break;
        case P_LOAD:  if (d > 0) openBrowser();                       break;
        case P_REC:   if (d > 0 && !recording) startRec();            break;
        default: break;
    }
}

static void valStr(int i, char *b, size_t n) {
    s32 tg = (gain * 2) / 5;
    switch (i) {
        case P_SPEED: snprintf(b, n, "%+ld%%", (long)speedPct); break;
        case P_PITCH: snprintf(b, n, "%+ld st", (long)semis); break;
        case P_SIZE:  snprintf(b, n, "%ld ms", (long)sizeMs); break;
        case P_DENS:  snprintf(b, n, "%ld /s", (long)density); break;
        case P_SPRAY: snprintf(b, n, "%ld ms", (long)sprayMs); break;
        case P_DRIFT: snprintf(b, n, "%ld%%", (long)driftPct); break;
        case P_HARM:  snprintf(b, n, "%ld%%", (long)harmPct); break;
        case P_JIT:   snprintf(b, n, "%ld cent", (long)jitterC); break;
        case P_REV:   snprintf(b, n, "%ld%%", (long)revPct); break;
        case P_REVERB: snprintf(b, n, "%ld%%", (long)revMixPct); break;
        case P_DECAY: snprintf(b, n, "%ld%%", (long)decayPct); break;
        case P_VOL:   snprintf(b, n, "%ld.%ld x", (long)(tg / 16), (long)((tg % 16) * 10 / 16)); break;
        case P_FADE:  snprintf(b, n, "%s", fadeTxt[fadeIdx]); break;
        case P_DROPFROM: snprintf(b, n, "%s", dropFromHead ? "la cabeza" : "el inicio"); break;
        case P_LOAD:  snprintf(b, n, "%s", sdOK ? "WAV de la SD >" : "sin SD"); break;
        default:      snprintf(b, n, "%s", recording ? "grabando..." : "pulsa Der"); break;
    }
}

static void fmtT(char *b, size_t n, u32 tenths) {
    snprintf(b, n, "%lu:%02lu.%lu", (unsigned long)(tenths / 600),
             (unsigned long)((tenths / 10) % 60), (unsigned long)(tenths % 10));
}

static void drawMain(bool full, s32 heardI) {
    consoleSelect(&top);
    if (full) iprintf("\x1b[2J");
    char a[20], b[20], v[24];
    iprintf("\x1b[0;0HGRANULAR %-9s %-6s\n", recording ? "REC..." : (playing ? "PLAY >" : "PAUSA ||"),
            dropOn ? "DROP" : (mixQ > 0 ? "~" : ""));
    iprintf("%-31.31s\n", curName);
    fmtT(a, sizeof a, (u32)heardI * 10 / srcRate);
    fmtT(b, sizeof b, srcLen * 10 / srcRate);
    iprintf("%s / %s  %luHz      \n", a, b, (unsigned long)srcRate);
    if (loopOn) {
        fmtT(a, sizeof a, (u32)loopStart * 10 / srcRate);
        fmtT(b, sizeof b, (u32)loopEnd * 10 / srcRate);
        iprintf("LOOP %s - %s      \n", a, b);
    } else {
        iprintf("loop off                   \n");
    }
    iprintf("\n");
    if (cur < pTop) pTop = cur;
    if (cur >= pTop + P_ROWS) pTop = cur - P_ROWS + 1;
    for (int r = 0; r < P_ROWS; r++) {
        int i = pTop + r;
        if (i >= P_COUNT) { iprintf("                               \n"); continue; }
        valStr(i, v, sizeof v);
        iprintf("%c%-8s %-14s%s\n", i == cur ? '>' : ' ', pLabel[i], v,
                (r == P_ROWS - 1 && pTop + P_ROWS < P_COUNT) ? "v" : (r == 0 && pTop > 0 ? "^" : " "));
    }
    iprintf("\x1b[19;0HSTART play  A DROP  B freeze  \n");
    iprintf("SELECT loop  X in  Y out    \n");
    iprintf("L/R salto 5s  toca onda=scrub\n");
    iprintf("^v elegir   <> cambiar valor\n");
    if (!sdOK) iprintf("\x1b[23;0H(SD no disponible: DLDI?)");
}

// ---------------------------------------------------------------- vista (pantalla tactil)
#define VW      256
#define VH      192
#define WAVE_H  160                  // filas de la onda; debajo, la barra de botones
#define BAR_Y   164
#define MID     86
#define AMP     70
#define STRIP   7                    // filas de arriba reservadas a los granos (la onda nunca llega ahi)

#define C_BG       ARGB16(1, 2, 2, 5)
#define C_LOOPBG   ARGB16(1, 2, 6, 4)
#define C_SPRAY    ARGB16(1, 5, 5, 10)
#define C_LOOPSPR  ARGB16(1, 5, 10, 8)
#define C_LOOPEDGE ARGB16(1, 4, 26, 10)
#define C_WAVE     ARGB16(1, 6, 22, 20)
#define C_PLAYED   ARGB16(1, 9, 13, 28)
#define C_GRAIN    ARGB16(1, 31, 31, 31)
#define C_CUR      ARGB16(1, 31, 28, 4)
#define C_CURDROP  ARGB16(1, 6, 29, 31)
#define C_TICK     ARGB16(1, 31, 12, 2)
#define C_BTN      ARGB16(1, 5, 5, 9)
#define C_BTNPLAY  ARGB16(1, 4, 18, 8)
#define C_BTNLOOP  ARGB16(1, 26, 22, 3)
#define C_BTNDROP  ARGB16(1, 3, 17, 24)
#define C_ICON     ARGB16(1, 28, 28, 30)
#define C_ICONDARK ARGB16(1, 2, 2, 5)

typedef struct { int cx, spr, gw, ls, le; bool lon, drop; } View;
static View lastV = { 0, 0, 1, 0, 0, false, false };
static bool lastPlaying = false, lastLoopOn = false, lastDrop = false;

static void computePeaks(void) {
    for (int x = 0; x < VW; x++) {
        u32 i0 = srcLen * (u32)x / VW;
        u32 i1 = srcLen * (u32)(x + 1) / VW;
        if (i1 <= i0) i1 = i0 + 1;
        u32 step = (i1 - i0) / 64;                   // maximo ~64 puntos por columna
        if (step < 1) step = 1;
        int mn = 127, mx = -127;
        for (u32 i = i0; i < i1 && i < srcLen; i += step) {
            int v = src[i];
            if (v < mn) mn = v;
            if (v > mx) mx = v;
        }
        if (mn > mx) mn = mx = 0;
        int ya = MID - mx * AMP / 127, yb = MID - mn * AMP / 127;
        if (ya > yb) { int t = ya; ya = yb; yb = t; }
        waveA[x] = (u8)ya;
        waveB[x] = (u8)yb;
    }
    fullRedraw = true;
}

static View viewNow(s32 heardI) {
    View v;
    v.cx  = (int)((u32)heardI * 256 / srcLen);
    if (v.cx > VW - 1) v.cx = VW - 1;
    v.spr = (int)((u32)(sprayMs * srcRate / 1000) * 256 / srcLen);
    v.gw  = (int)((u32)(sizeMs * srcRate / 1000) * 256 / srcLen);
    if (v.gw < 1) v.gw = 1;
    v.ls  = (int)((u32)loopStart * 256 / srcLen);
    v.le  = (int)((u32)loopEnd * 256 / srcLen);
    v.lon = loopOn;
    v.drop = dropOn;
    return v;
}

static void drawColumn(int x, const View *v) {
    u16 *p = fb + x;
    if (x == v->cx) {
        u16 cc = v->drop ? C_CURDROP : C_CUR;
        for (int y = 0; y < WAVE_H; y++, p += VW) *p = cc;
        return;
    }
    bool inLoop  = v->lon && x >= v->ls && x <= v->le;
    bool inSpray = x >= v->cx - v->spr && x <= v->cx + v->spr;
    u16 bg = inLoop ? (inSpray ? C_LOOPSPR : C_LOOPBG) : (inSpray ? C_SPRAY : C_BG);
    if (v->lon && (x == v->ls || x == v->le)) bg = C_LOOPEDGE;
    u16 wv = (x >= v->cx && x < v->cx + v->gw) ? C_GRAIN : (x < v->cx ? C_PLAYED : C_WAVE);
    for (int y = 0; y < WAVE_H; y++, p += VW) *p = (y >= waveA[x] && y <= waveB[x]) ? wv : bg;
}

static void drawRange(int x0, int x1, const View *v) {
    if (x0 < 0) x0 = 0;
    if (x1 > VW - 1) x1 = VW - 1;
    for (int x = x0; x <= x1; x++) drawColumn(x, v);
}

static void drawStrip(const View *v) {
    for (int x = 0; x < VW; x++) {
        bool inLoop  = v->lon && x >= v->ls && x <= v->le;
        bool inSpray = x >= v->cx - v->spr && x <= v->cx + v->spr;
        u16 c = (x == v->cx) ? (v->drop ? C_CURDROP : C_CUR)
              : inLoop ? (inSpray ? C_LOOPSPR : C_LOOPBG)
              : (inSpray ? C_SPRAY : C_BG);
        u16 *p = fb + x;
        for (int y = 0; y < STRIP; y++, p += VW) *p = c;
    }
    for (int g = 0; g < MAX_GRAINS; g++) {
        if (!grains[g].on || grains[g].ipos >= srcLen) continue;
        int gx = (int)(grains[g].ipos * 256 / srcLen);
        u16 *p = fb + gx;
        for (int y = 0; y < STRIP - 1; y++, p += VW) *p = C_TICK;
    }
}

static void fillRect(int x, int y, int w, int h, u16 c) {
    for (int j = 0; j < h; j++) {
        u16 *p = fb + (y + j) * VW + x;
        for (int i = 0; i < w; i++) p[i] = c;
    }
}

// triangulo relleno apuntando a la derecha (dir=+1) o a la izquierda (dir=-1), 14 filas
static void fillTri(int x, int y, int dir, u16 c) {
    for (int r = 0; r < 14; r++) {
        int w = (r < 7 ? r + 1 : 14 - r) * 2;
        if (dir > 0) fillRect(x, y + r, w, 1, c);
        else         fillRect(x - w, y + r, w, 1, c);
    }
}

// 5 botones de 46 px, paso 50: x = 4, 54, 104, 154, 204. Cortes del toque en main: 52, 102, 152, 202.
static void drawButtons(void) {
    fillRect(0, WAVE_H, VW, VH - WAVE_H, C_ICONDARK);
    int cx;

    // [play / pausa]
    cx = 4 + 23;
    fillRect(4, 166, 46, 24, playing ? C_BTNPLAY : C_BTN);
    if (playing) { fillRect(cx - 10, 171, 6, 14, C_ICON); fillRect(cx + 4, 171, 6, 14, C_ICON); }
    else         { fillTri(cx - 6, 171, +1, C_ICON); }

    // [loop]: corchetes
    cx = 54 + 23;
    u16 lc = loopOn ? C_ICONDARK : C_ICON;
    fillRect(54, 166, 46, 24, loopOn ? C_BTNLOOP : C_BTN);
    fillRect(cx - 14, 171, 3, 14, lc); fillRect(cx - 14, 171, 6, 3, lc); fillRect(cx - 14, 182, 6, 3, lc);
    fillRect(cx + 11, 171, 3, 14, lc); fillRect(cx + 8, 171, 6, 3, lc);  fillRect(cx + 8, 182, 6, 3, lc);
    fillRect(cx - 3, 176, 6, 4, lc);

    // [al inicio]: barra + triangulo a la izquierda
    cx = 104 + 23;
    fillRect(104, 166, 46, 24, C_BTN);
    fillRect(cx - 12, 171, 3, 14, C_ICON);
    fillTri(cx + 8, 171, -1, C_ICON);

    // [carpeta]: abre el navegador de la SD
    cx = 154 + 23;
    fillRect(154, 166, 46, 24, C_BTN);
    fillRect(cx - 12, 173, 9, 3, C_ICON);      // solapa
    fillRect(cx - 12, 176, 24, 12, C_ICON);    // cuerpo

    // [DROP]: flecha hacia abajo
    cx = 204 + 23;
    u16 dc = dropOn ? C_ICONDARK : C_ICON;
    fillRect(204, 166, 46, 24, dropOn ? C_BTNDROP : C_BTN);
    fillRect(cx - 3, 169, 6, 8, dc);
    for (int r = 0; r < 8; r++) fillRect(cx - 8 + r, 177 + r, 16 - 2 * r, 1, dc);

    lastPlaying = playing;
    lastLoopOn = loopOn;
    lastDrop = dropOn;
}

static void updateView(s32 heardI) {
    View v = viewNow(heardI);
    bool loopChanged = (v.lon != lastV.lon) || (v.lon && (v.ls != lastV.ls || v.le != lastV.le));
    if (fullRedraw || loopChanged) {
        drawRange(0, VW - 1, &v);
        drawButtons();
        fullRedraw = false;
    } else {
        if (v.cx != lastV.cx || v.spr != lastV.spr || v.gw != lastV.gw || v.drop != lastV.drop) {
            int ext0 = lastV.gw > lastV.spr ? lastV.gw : lastV.spr;
            int ext1 = v.gw > v.spr ? v.gw : v.spr;
            int l0 = lastV.cx - lastV.spr, r0 = lastV.cx + ext0;
            int l1 = v.cx - v.spr,         r1 = v.cx + ext1;
            drawRange(l0 < l1 ? l0 : l1, r0 > r1 ? r0 : r1, &v);   // solo lo que cambio
        }
        if (playing != lastPlaying || loopOn != lastLoopOn || dropOn != lastDrop) drawButtons();
    }
    lastV = v;
    drawStrip(&v);
}

// donde esta la cabeza segun lo que SE ESCUCHA (el audio se renderiza ~47 ms por delante)
static s32 heardPos(u32 ahead) {
    s32 h;
    if (dropOn || mixQ > MIX_FULL / 2) {                    // se oye sobre todo el track limpio
        h = trackI;
        if (playing && !recording) h -= (s32)(((u32)ahead * cleanInc) >> 16);
    } else {
        h = posI;
        if (playing && !touching && !freezeKey && !recording) h -= (s32)(((s32)ahead * scanInc) >> 16);
    }
    return clampi(h, 0, (s32)srcLen - 1);
}

// ---------------------------------------------------------------- main
int main(void) {
    // arriba: consola de texto (parametros / navegador). abajo: bitmap con la forma de onda
    videoSetMode(MODE_0_2D);
    videoSetModeSub(MODE_5_2D | DISPLAY_BG3_ACTIVE);
    vramSetBankA(VRAM_A_MAIN_BG);
    vramSetBankC(VRAM_C_SUB_BG);
    consoleInit(&top, 0, BgType_Text4bpp, BgSize_T_256x256, 31, 0, true, true);
    int bgSub = bgInitSub(3, BgType_Bmp16, BgSize_B16_256x256, 0, 0);
    fb = (u16 *)bgGetGfxPtr(bgSub);
    consoleSelect(&top);

    sdOK = fatInitDefault();
    soundEnable();

    for (int i = 0; i < OUT_LEN; i++) out[i] = 0;
    // sample inicial: sierra ~220 Hz con decaimiento, para sonar antes de cargar nada
    for (int i = 0; i < REC_LEN; i++)
        recBuf[i] = (s8)(((((i % 73) * 400 - 14600) * (REC_LEN - i)) / REC_LEN) >> 8);
    for (int i = 0; i < WIN_LEN; i++)        // ventana Hann en Q15
        win[i] = (s16)(32767.0f * 0.5f * (1.0f - cosf(6.2831853f * i / (WIN_LEN - 1))));
    win[WIN_LEN] = 0;
    harmRatio[0] = (s32)(65536.0f * exp2f(-12.0f / 12.0f));
    harmRatio[1] = (s32)(65536.0f * exp2f(-5.0f / 12.0f));
    harmRatio[2] = (s32)(65536.0f * exp2f(7.0f / 12.0f));
    harmRatio[3] = (s32)(65536.0f * exp2f(12.0f / 12.0f));
    updateReverb();
    updateInc();
    resetTransport(true, true);
    computePeaks();

    DC_FlushRange(out, sizeof(out));
    soundPlaySample(out, SoundFormat_16Bit, sizeof(out), OUT_RATE, 127, 64, true, 0);

    // reloj del playhead: 33.514 MHz / 64 = 523656 Hz = 16 ticks por muestra de salida
    TIMER_DATA(0) = 0;
    TIMER_CR(0) = TIMER_ENABLE | TIMER_DIV_64;

    u32 wr = LEAD, frame = 0;
    bool uiDirty = true;
    keysSetRepeat(15, 3);
    drawMain(true, posI);

    while (1) {
        swiWaitForVBlank();
        scanKeys();
        u32 kd = keysDown(), kh = keysHeld(), kr = keysDownRepeat();
        if (kd | kr) uiDirty = true;

        if (browsing) {
            touching = false; freezeKey = false; touchDrag = false;
            bool dirty = false;
            if ((kr & KEY_UP)   && sel > 0)        { sel--; dirty = true; }
            if ((kr & KEY_DOWN) && sel < nEnt - 1) { sel++; dirty = true; }
            if (sel < scrollTop) scrollTop = sel;
            if (sel >= scrollTop + 19) scrollTop = sel - 18;
            if (kd & KEY_B) { browsing = false; drawMain(true, curPos()); }
            else if ((kd & KEY_A) && nEnt > 0) {
                if (ents[sel].dir) {
                    chdir(ents[sel].name);
                    scanDir();
                    dirty = true;
                } else {
                    // silenciamos el anillo: la carga tarda segundos y no renderizamos
                    playing = false;
                    for (int i = 0; i < OUT_LEN; i++) out[i] = 0;
                    DC_FlushRange(out, sizeof(out));
                    consoleSelect(&top);
                    iprintf("\x1b[2J\x1b[10;0H  cargando...\n  %.28s", ents[sel].name);
                    const char *err = loadWav(ents[sel].name);
                    u32 ph = (TIMER_DATA(0) >> 4) & (OUT_LEN - 1);
                    wr = (ph + LEAD) & (OUT_LEN - 1);          // re-sincroniza con el playhead
                    consoleSelect(&top);
                    if (err) {
                        if (lostSample) useRec("[demo/mic]");   // la carga fallida nos dejo sin sample
                        iprintf("\x1b[2J\x1b[10;0H  error: %s\n\n  (A para volver)", err);
                        while (1) { swiWaitForVBlank(); scanKeys(); if (keysDown() & (KEY_A | KEY_B)) break; }
                        drawBrowser();
                    } else {
                        browsing = false;
                        drawMain(true, curPos());
                    }
                    dirty = false;
                }
            }
            if (dirty) drawBrowser();
        } else if (recording) {
            touching = false; freezeKey = false; touchDrag = false;
            if (micDone) { finishRec(); drawMain(true, posI); uiDirty = false; }
        } else {
            freezeKey = (kh & KEY_B) != 0;
            if (kd & KEY_START)  togglePlay();
            if (kd & KEY_A)      toggleDrop();
            if (kd & KEY_SELECT) toggleLoop();
            if (kd & KEY_X)      { loopStart = curPos(); fixLoop(true); }
            if (kd & KEY_Y)      { loopEnd = curPos(); fixLoop(false); loopOn = true; }
            if (kr & KEY_L)      seekRel(-5 * (s32)srcRate);
            if (kr & KEY_R)      seekRel(5 * (s32)srcRate);
            if (kr & KEY_UP)     cur = (cur + P_COUNT - 1) % P_COUNT;
            if (kr & KEY_DOWN)   cur = (cur + 1) % P_COUNT;
            if (kr & KEY_LEFT)   adjust(-1);
            if (kr & KEY_RIGHT)  adjust(+1);

            // pantalla tactil: botones abajo, scrub en la onda
            if (!browsing && (kh & KEY_TOUCH)) {
                touchPosition t;
                touchRead(&t);
                if (kd & KEY_TOUCH) {
                    if (t.py >= BAR_Y) {
                        touchDrag = false;
                        if (t.px < 52)       togglePlay();
                        else if (t.px < 102) toggleLoop();
                        else if (t.px < 152) { if (dropOn) { trackI = 0; trackF = 0; } else seekTo(loopOn ? loopStart : 0); }
                        else if (t.px < 202) openBrowser();
                        else                 toggleDrop();
                    } else {
                        touchDrag = true;
                        if (dropOn) toggleDrop();                // tocar la onda recupera el control de la nube
                    }
                }
                if (touchDrag) seekTo((s32)((u32)t.px * (srcLen - 1) / 255));
            } else {
                touchDrag = false;
            }
            touching = touchDrag;
        }

        // render por delante del playhead
        u32 ph = (TIMER_DATA(0) >> 4) & (OUT_LEN - 1);
        while (((wr - ph) & (OUT_LEN - 1)) < LEAD) {
            render(&out[wr], CHUNK);
            DC_FlushRange(&out[wr], CHUNK * 2);
            wr = (wr + CHUNK) & (OUT_LEN - 1);
        }

        // interfaz: despues del audio, el sonido tiene prioridad
        s32 hp = heardPos((wr - ph) & (OUT_LEN - 1));
        updateView(hp);
        if (uiDirty || (++frame & 7) == 0) {
            if (!browsing) drawMain(false, hp);
            uiDirty = false;
        }
    }
    return 0;
}
