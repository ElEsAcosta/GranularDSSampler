// granular.c - sampler granular para Nintendo DS/DSi (libnds + libfat, ARM9)
//
// Pantalla de arriba: parametros / navegador de la SD
// Pantalla tactil   : posicion (X) y tamano de grano (Y)
//
// SELECT      : abrir navegador de la SD (carpetas + .wav, hasta 3 min)
// A           : grabar 2 s del microfono
// Izq / Der   : pitch en semitonos (-24..+24)
// Arr / Abajo : densidad (granos por segundo)
// L / R       : spray (aleatoriedad de posicion, 0..500 ms)
// B + Izq/Der : mover la posicion de lectura de a 50 ms (ajuste fino)
//
// En el navegador: Arr/Abajo mover, A abrir/cargar, B cancelar.
//
// WAV soportados: PCM 8/16/24 bit, mono o estereo, cualquier frecuencia.
// Se mezcla a mono y se guarda en 8 bit; si el archivo no cabe en RAM
// (la DS tiene 4 MB) se reduce la frecuencia de muestreo automaticamente.

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
#define MAX_GRAINS  8
#define WIN_LEN     256

#define REC_RATE    16000   // frecuencia del mic
#define REC_LEN     (REC_RATE * 2)

#define MAX_SECS    180     // limite: 3 minutos
#define BUDGET      2900000 // bytes de RAM para el sample (8 bit)

typedef struct { u32 pos, inc, wpos, winc; bool on; } Grain;

static Grain grains[MAX_GRAINS];
static s16 out[OUT_LEN] __attribute__((aligned(32)));
static u8  mic[REC_LEN] __attribute__((aligned(32)));
static s8  recBuf[REC_LEN];          // sample inicial / grabacion del mic
static s16 win[WIN_LEN];

static s8  *src = recBuf, *heapBuf = NULL;   // sample activo (s8)
static u32 srcLen = REC_LEN, srcRate = REC_RATE;
static char curName[128] = "[demo]";

static s32 centre = REC_LEN / 2, sizeMs = 80, semis = 0, density = 20, sprayMs = 50;
static u32 inc16, rng = 2463534242u;
static s32 untilSpawn = 1;
static volatile bool micDone = false;
static bool recording = false, sdOK = false;

static PrintConsole top, bot;

static u32 rnd(void) { rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5; return rng; }

static u16 rd16(const u8 *p) { return (u16)(p[0] | (p[1] << 8)); }
static u32 rd32(const u8 *p) { return (u32)p[0] | ((u32)p[1] << 8) | ((u32)p[2] << 16) | ((u32)p[3] << 24); }

// incremento de lectura en 16.16 (frecuencia del sample -> salida ~32.7 kHz, mas pitch)
static void updateInc(void) {
    inc16 = (u32)(65536.0f * ((float)srcRate / 32728.5f) * exp2f(semis / 12.0f));
}

static void killGrains(void) {
    for (int g = 0; g < MAX_GRAINS; g++) grains[g].on = false;
    untilSpawn = 1;
}

static void spawn(void) {
    for (int g = 0; g < MAX_GRAINS; g++) {
        if (grains[g].on) continue;
        s32 sp = (s32)(sprayMs * srcRate / 1000);
        s32 start = centre + (s32)(rnd() % (2 * sp + 1)) - sp;
        if (start < 0) start = 0;
        if (start >= (s32)srcLen) start = srcLen - 1;
        u32 len = (u32)(sizeMs * OUT_RATE / 1000);
        grains[g].pos  = (u32)start << 16;
        grains[g].inc  = inc16;
        grains[g].wpos = 0;
        grains[g].winc = ((u32)WIN_LEN << 16) / len;
        grains[g].on   = true;
        return;
    }
}

// todo en enteros: el ARM9 no tiene FPU
static void render(s16 *dst, int n) {
    for (int i = 0; i < n; i++) {
        if (recording) { dst[i] = 0; continue; }
        if (--untilSpawn <= 0) { spawn(); untilSpawn = OUT_RATE / density; }

        s32 acc = 0;
        for (int g = 0; g < MAX_GRAINS; g++) {
            Grain *gr = &grains[g];
            if (!gr->on) continue;
            u32 si = gr->pos >> 16;
            if (si + 1 >= srcLen || gr->wpos >= ((u32)WIN_LEN << 16)) { gr->on = false; continue; }
            s32 a = src[si], b = src[si + 1];
            s32 s = a + (((b - a) * (s32)((gr->pos >> 8) & 0xFF)) >> 8);   // interpolacion lineal
            acc += (s * win[gr->wpos >> 16]) >> 7;                          // s8 -> s16 con ventana Q15
            gr->pos  += gr->inc;
            gr->wpos += gr->winc;
        }
        acc >>= 1;
        if (acc > 32767) acc = 32767;
        if (acc < -32768) acc = -32768;
        dst[i] = (s16)acc;
    }
}

// ---------------------------------------------------------------- sample
static void freeHeap(void) { if (heapBuf) { free(heapBuf); heapBuf = NULL; } }

static void useRec(const char *name) {
    freeHeap();
    src = recBuf; srcLen = REC_LEN; srcRate = REC_RATE;
    centre = srcLen / 2;
    strncpy(curName, name, sizeof(curName) - 1);
    updateInc();
    killGrains();
}

// ---------------------------------------------------------------- microfono
static void micCb(void *buf, int len) { (void)buf; (void)len; micDone = true; }

static void startRec(void) {
    killGrains();
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

// ---------------------------------------------------------------- WAV
// devuelve NULL si todo bien, o un mensaje de error
static const char *loadWav(const char *name) {
    FILE *f = fopen(name, "rb");
    if (!f) return "no se pudo abrir";

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
    freeHeap();
    src = recBuf; srcLen = REC_LEN; srcRate = REC_RATE;

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
                if (j < outLen) buf[j++] = (s8)((acc / (s32)cnt) >> 8);
                acc = 0; cnt = 0;
            }
        }
        done += n;
        if ((++nb & 31) == 0) iprintf("\x1b[12;0H  %3lu%%", (unsigned long)(done / (frames / 100 + 1)));
    }
    free(blk);
    fclose(f);

    if (j < 256) { free(buf); return "error leyendo la SD"; }

    heapBuf = buf; src = buf; srcLen = j; srcRate = storeRate;
    centre = srcLen / 2;
    strncpy(curName, name, sizeof(curName) - 1);
    updateInc();
    killGrains();
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

static void drawMain(bool full) {
    consoleSelect(&top);
    if (full) iprintf("\x1b[2J");
    iprintf("\x1b[0;0H");
    iprintf("GRANULAR %s\n", recording ? "[REC...]" : "        ");
    iprintf("%-31.31s\n", curName);
    iprintf("%lu.%lu s @ %lu Hz       \n\n", (unsigned long)(srcLen * 10 / srcRate / 10),
            (unsigned long)(srcLen * 10 / srcRate % 10), (unsigned long)srcRate);
    iprintf("pos     %4lu.%lu s \n", (unsigned long)(centre * 10 / srcRate / 10),
            (unsigned long)(centre * 10 / srcRate % 10));
    iprintf("tamano  %5ld ms \n", (long)sizeMs);
    iprintf("pitch   %+5ld st \n", (long)semis);
    iprintf("densid. %5ld /s \n", (long)density);
    iprintf("spray   %5ld ms \n", (long)sprayMs);
    if (!sdOK) iprintf("\n(SD no disponible: DLDI?)\n");
}

// ---------------------------------------------------------------- main
int main(void) {
    videoSetMode(MODE_0_2D);
    videoSetModeSub(MODE_0_2D);
    vramSetBankA(VRAM_A_MAIN_BG);
    vramSetBankC(VRAM_C_SUB_BG);
    consoleInit(&top, 0, BgType_Text4bpp, BgSize_T_256x256, 31, 0, true,  true);
    consoleInit(&bot, 0, BgType_Text4bpp, BgSize_T_256x256, 31, 0, false, true);

    consoleSelect(&bot);
    iprintf("\n  toca aqui:\n\n  X = posicion\n  Y = tamano de grano\n\n");
    iprintf("  SELECT = cargar WAV\n  A      = grabar mic\n  B+<>   = ajuste fino\n");
    consoleSelect(&top);

    sdOK = fatInitDefault();
    soundEnable();

    for (int i = 0; i < OUT_LEN; i++) out[i] = 0;
    // sample inicial: sierra ~220 Hz con decaimiento, para sonar antes de cargar nada
    for (int i = 0; i < REC_LEN; i++)
        recBuf[i] = (s8)(((((i % 73) * 400 - 14600) * (REC_LEN - i)) / REC_LEN) >> 8);
    for (int i = 0; i < WIN_LEN; i++)        // ventana Hann en Q15
        win[i] = (s16)(32767.0f * 0.5f * (1.0f - cosf(6.2831853f * i / (WIN_LEN - 1))));
    updateInc();

    DC_FlushRange(out, sizeof(out));
    soundPlaySample(out, SoundFormat_16Bit, sizeof(out), OUT_RATE, 127, 64, true, 0);

    // reloj del playhead: 33.514 MHz / 64 = 523656 Hz = 16 ticks por muestra de salida
    TIMER_DATA(0) = 0;
    TIMER_CR(0) = TIMER_ENABLE | TIMER_DIV_64;

    u32 wr = LEAD;
    bool browsing = false;
    keysSetRepeat(15, 3);
    drawMain(true);

    while (1) {
        swiWaitForVBlank();
        scanKeys();
        u32 kd = keysDown(), kh = keysHeld(), kr = keysDownRepeat();

        if (browsing) {
            bool dirty = false;
            if ((kr & KEY_UP)   && sel > 0)        { sel--; dirty = true; }
            if ((kr & KEY_DOWN) && sel < nEnt - 1) { sel++; dirty = true; }
            if (sel < scrollTop) scrollTop = sel;
            if (sel >= scrollTop + 19) scrollTop = sel - 18;
            if (kd & KEY_B) { browsing = false; drawMain(true); }
            else if ((kd & KEY_A) && nEnt > 0) {
                if (ents[sel].dir) {
                    chdir(ents[sel].name);
                    scanDir();
                    dirty = true;
                } else {
                    // silenciamos el anillo: la carga tarda segundos y no renderizamos
                    for (int i = 0; i < OUT_LEN; i++) out[i] = 0;
                    DC_FlushRange(out, sizeof(out));
                    consoleSelect(&top);
                    iprintf("\x1b[2J\x1b[10;0H  cargando...\n  %.28s", ents[sel].name);
                    const char *err = loadWav(ents[sel].name);
                    u32 ph = (TIMER_DATA(0) >> 4) & (OUT_LEN - 1);
                    wr = (ph + LEAD) & (OUT_LEN - 1);          // re-sincroniza con el playhead
                    consoleSelect(&top);
                    if (err) {
                        iprintf("\x1b[2J\x1b[10;0H  error: %s\n\n  (A para volver)", err);
                        while (1) { swiWaitForVBlank(); scanKeys(); if (keysDown() & (KEY_A | KEY_B)) break; }
                        drawBrowser();
                    } else {
                        browsing = false;
                        drawMain(true);
                    }
                    dirty = false;
                }
            }
            if (dirty) drawBrowser();
        } else if (recording) {
            if (micDone) { finishRec(); drawMain(true); }
        } else {
            if (kd & KEY_A) { startRec(); drawMain(false); }
            if (kd & KEY_SELECT) {
                if (sdOK) { scanDir(); browsing = true; drawBrowser(); }
            }
            if (kh & KEY_TOUCH) {
                touchPosition t; touchRead(&t);
                centre = (s32)((u32)t.px * (srcLen - 1) / 255);
                sizeMs = 10 + t.py * 290 / 192;
            }
            if (kh & KEY_B) {                                   // ajuste fino de posicion
                s32 step = (s32)(50 * srcRate / 1000);
                if (kr & KEY_RIGHT) centre += step;
                if (kr & KEY_LEFT)  centre -= step;
                if (centre < 0) centre = 0;
                if (centre > (s32)srcLen - 1) centre = srcLen - 1;
            } else {
                if (kr & KEY_RIGHT) { if (semis < 24)  semis++; updateInc(); }
                if (kr & KEY_LEFT)  { if (semis > -24) semis--; updateInc(); }
            }
            if (kr & KEY_UP)    { if (density < 100) density += 2; }
            if (kr & KEY_DOWN)  { if (density > 2)   density -= 2; }
            if (kr & KEY_R)     { if (sprayMs < 500) sprayMs += 10; }
            if (kr & KEY_L)     { if (sprayMs > 0)   sprayMs -= 10; }
            drawMain(false);
        }

        // render por delante del playhead
        u32 ph = (TIMER_DATA(0) >> 4) & (OUT_LEN - 1);
        while (((wr - ph) & (OUT_LEN - 1)) < LEAD) {
            render(&out[wr], CHUNK);
            DC_FlushRange(&out[wr], CHUNK * 2);
            wr = (wr + CHUNK) & (OUT_LEN - 1);
        }
    }
    return 0;
}
