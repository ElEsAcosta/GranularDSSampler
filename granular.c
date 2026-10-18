// granular.c - sampler granular para tracks enteros en Nintendo DS/DSi (libnds + libfat, ARM9)
//
// Idea: la "cabeza de lectura" avanza sola por el track (play), y alrededor de ella se
// disparan granos. Velocidad y pitch son independientes: puedes estirar, congelar o
// invertir el track sin cambiar el tono (o al reves). Con DROP sueltas el track entero,
// limpio, sin ninguna modificacion, y puedes volver a la nube desde donde va la cancion.
//
// PANTALLA DE ABAJO (tactil): forma de onda en tiempo real
//   toca / arrastra la onda : scrub (suena aunque estes en pausa; si estabas en DROP, lo suelta)
//   botones: [play/pausa] [loop] [inicio] [SD = cargar WAV] [DROP]
//   linea naranja = cabeza de lectura (blanca en DROP), onda amarilla = ya reproducido, gris = por tocar,
//   fondo calido = region de loop, banda clara = spray, onda blanca = ancho de un grano,
//   marcas amarillas arriba = granos sonando
// Paleta: grises, amarillo claro, blanco y naranja. Las dos pantallas son bitmaps con fuente propia.
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
//   ARMONIA 0..100 % de granos transpuestos a -12/-5/+7/+12
//   JITTER 0..100 cents   REVERSA 0..100 % de granos al reves
//   REVERB 0..100 % mezcla   COLA 0..100 (largo de la cola, hasta ~10 s)
//   ESTEREO 0..100  cuanto se abre la nube en el panorama (cada grano cae en un lugar distinto)
//   SHIMMER 0..100  granos en octavas (+12/+24/+19/-12) que suben y bajan solos (~17 s) y suenan sobre todo
//                   dentro de la reverb, como un pad brillante
//   FILTRO  pasa-bajos de toda la salida (40 Hz .. 9 kHz; 100 = abierto)   BARRIDO 0..100 profundidad de un
//                   barrido lento y automatico del filtro (~12 s por ciclo)
//   VOLUMEN (el volumen automatico sube solo los tracks flojos; 1.0x = nivel base)   FUNDIDO 0.05..16 s (duracion del DROP)
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
#define LEAD        1792    // cuanto renderizamos por delante del playhead (~55 ms)
#define RESYNC      (LEAD + 3 * CHUNK)   // si el adelanto parece mayor, el playhead nos paso: resincronizar
#define MAX_GRAINS  16
#define WIN_LEN     256

#define REC_RATE    16000   // frecuencia del mic
#define REC_LEN     (REC_RATE * 2)

#define MAX_SECS    180     // limite: 3 minutos
#define BUDGET      2900000 // bytes de RAM para el sample (8 bit)

#define MIX_FULL    (1 << 24)   // mezcla del DROP en Q24: 0 = solo nube, MIX_FULL = solo track limpio

// posicion del grano = indice entero (u32) + fraccion de 16 bit; el indice necesita mas de
// 16 bit porque un track de 3 min tiene millones de muestras
typedef struct { u32 ipos; s32 fpos; s32 inc; u32 wpos, winc; s32 pl, pr, amp; bool on, shim; } Grain;

static Grain grains[MAX_GRAINS];
static s16 outL[OUT_LEN] __attribute__((aligned(32)));     // anillos de audio: izquierdo y derecho
static s16 outR[OUT_LEN] __attribute__((aligned(32)));
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
static s32 panPct = 60, shimPct = 0, filtPct = 100, sweepPct = 0;
static s32 gain = 40;                // volumen de la nube, Q4; el track limpio usa gain*2/5 (40 = 1.0x)
static u32 inc16;                    // pitch: incremento de lectura de un grano (16.16)
static u32 cleanInc;                 // lectura 1x del track limpio (16.16)
static s32 scanInc;                  // velocidad: avance de la cabeza por muestra de salida (16.16, con signo)
static s32 autoQ = 256;              // ganancia automatica del track (Q8): sube los tracks flojos
static s32 gainC = 40, gainT = 16;   // ganancia efectiva de la nube y del track limpio
static s32 normQ = 256;              // compensacion por solapamiento de granos (Q8)
static s32 fadeStep = 1000;          // avance de mixQ por muestra
static s32 harmRatio[4];             // razones Q16 de -12, -5, +7, +12 semitonos
static s32 driftW = 0;               // caminata aleatoria de la posicion

static u32 rng = 2463534242u;
static s32 untilSpawn = 1;
static volatile bool micDone = false;
static bool recording = false, sdOK = false;
static bool browsing = false, touchDrag = false;     // navegador de la SD abierto / arrastre en la onda

static u8 waveA[256], waveB[256];     // por columna: fila superior / inferior de la onda
static bool fullRedraw = true;

static void computePeaks(void);       // definida mas abajo (vista)

static u32 rnd(void) { rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5; return rng; }
static s32 clampi(s32 v, s32 lo, s32 hi) { return v < lo ? lo : (v > hi ? hi : v); }
static s32 clamp16(s32 v) { return v > 32767 ? 32767 : (v < -32768 ? -32768 : v); }

static u16 rd16(const u8 *p) { return (u16)(p[0] | (p[1] << 8)); }
static u32 rd32(const u8 *p) { return (u32)p[0] | ((u32)p[1] << 8) | ((u32)p[2] << 16) | ((u32)p[3] << 24); }

// ---------------------------------------------------------------- graficos
// Las dos pantallas son bitmaps de 16 bit de 256x192. El texto usa una fuente propia de 6x10.
#define VW      256
#define VH      192

static u16 *fb;                       // pantalla de abajo (tactil): onda y botones
static u16 *fbTop;                    // pantalla de arriba: parametros / navegador

#define RGB8(r, g, b) ARGB16(1, (r) >> 3, (g) >> 3, (b) >> 3)

// paleta: grises, amarillo claro, blanco y naranja
#define C_DARK     RGB8( 24,  24,  27)
#define C_BG       RGB8( 32,  32,  36)
#define C_PANEL    RGB8( 46,  46,  51)
#define C_PANEL2   RGB8( 62,  62,  69)
#define C_LINE     RGB8( 84,  84,  92)
#define C_GRAY     RGB8(146, 146, 154)
#define C_LGRAY    RGB8(204, 204, 210)
#define C_WHITE    RGB8(255, 255, 255)
#define C_YEL      RGB8(248, 235, 170)      // amarillo claro
#define C_YELD     RGB8(190, 176, 112)
#define C_ORG      RGB8(255, 140,  32)      // naranja
#define C_ORGD     RGB8(176,  92,  20)

#define FONT_W 6
#define FONT_H 10
static const u8 font6[95][FONT_H] = {
    {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},  //  
    {0x00,0x04,0x04,0x04,0x04,0x04,0x00,0x04,0x00,0x00},  // !
    {0x00,0x0A,0x0A,0x0A,0x00,0x00,0x00,0x00,0x00,0x00},  // "
    {0x00,0x0A,0x0A,0x1F,0x14,0x3E,0x14,0x14,0x00,0x00},  // #
    {0x00,0x04,0x0F,0x14,0x1C,0x07,0x05,0x1E,0x04,0x00},  // $
    {0x00,0x38,0x28,0x3A,0x0C,0x17,0x05,0x07,0x00,0x00},  // %
    {0x00,0x0E,0x08,0x0C,0x15,0x13,0x12,0x0D,0x00,0x00},  // &
    {0x00,0x04,0x04,0x04,0x00,0x00,0x00,0x00,0x00,0x00},  // '
    {0x04,0x08,0x08,0x08,0x08,0x08,0x08,0x08,0x04,0x00},  // (
    {0x08,0x08,0x04,0x04,0x04,0x04,0x04,0x08,0x08,0x00},  // )
    {0x00,0x15,0x0E,0x0E,0x15,0x00,0x00,0x00,0x00,0x00},  // *
    {0x00,0x00,0x04,0x04,0x1F,0x04,0x04,0x00,0x00,0x00},  // +
    {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x08,0x08,0x08},  // ,
    {0x00,0x00,0x00,0x00,0x00,0x0E,0x00,0x00,0x00,0x00},  // -
    {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x08,0x00,0x00},  // .
    {0x00,0x01,0x02,0x02,0x04,0x04,0x08,0x08,0x10,0x00},  // /
    {0x00,0x0E,0x11,0x11,0x15,0x11,0x11,0x0E,0x00,0x00},  // 0
    {0x00,0x1C,0x04,0x04,0x04,0x04,0x04,0x1F,0x00,0x00},  // 1
    {0x00,0x0E,0x11,0x01,0x03,0x06,0x08,0x1F,0x00,0x00},  // 2
    {0x00,0x0E,0x11,0x01,0x0E,0x01,0x11,0x0E,0x00,0x00},  // 3
    {0x00,0x02,0x06,0x0A,0x1A,0x1F,0x02,0x02,0x00,0x00},  // 4
    {0x00,0x1E,0x10,0x1E,0x01,0x01,0x01,0x1E,0x00,0x00},  // 5
    {0x00,0x0F,0x18,0x10,0x1E,0x11,0x11,0x0E,0x00,0x00},  // 6
    {0x00,0x1F,0x03,0x02,0x02,0x04,0x04,0x08,0x00,0x00},  // 7
    {0x00,0x0E,0x11,0x11,0x0E,0x11,0x11,0x0E,0x00,0x00},  // 8
    {0x00,0x0E,0x11,0x11,0x0F,0x01,0x03,0x1E,0x00,0x00},  // 9
    {0x00,0x00,0x00,0x08,0x00,0x00,0x00,0x08,0x00,0x00},  // :
    {0x00,0x00,0x00,0x08,0x00,0x00,0x00,0x08,0x08,0x08},  // ;
    {0x00,0x00,0x01,0x0E,0x10,0x0E,0x01,0x00,0x00,0x00},  // <
    {0x00,0x00,0x00,0x3E,0x00,0x3E,0x00,0x00,0x00,0x00},  // =
    {0x00,0x00,0x10,0x0E,0x01,0x0E,0x10,0x00,0x00,0x00},  // >
    {0x00,0x1E,0x02,0x04,0x08,0x08,0x00,0x08,0x00,0x00},  // ?
    {0x00,0x0E,0x09,0x17,0x15,0x15,0x15,0x17,0x08,0x06},  // @
    {0x00,0x04,0x04,0x0A,0x0A,0x0E,0x11,0x11,0x00,0x00},  // A
    {0x00,0x1E,0x11,0x11,0x1E,0x11,0x11,0x1E,0x00,0x00},  // B
    {0x00,0x0F,0x19,0x10,0x10,0x10,0x19,0x0F,0x00,0x00},  // C
    {0x00,0x1E,0x13,0x11,0x11,0x11,0x13,0x1E,0x00,0x00},  // D
    {0x00,0x1F,0x10,0x10,0x1F,0x10,0x10,0x1F,0x00,0x00},  // E
    {0x00,0x1F,0x10,0x10,0x1F,0x10,0x10,0x10,0x00,0x00},  // F
    {0x00,0x0E,0x19,0x10,0x13,0x11,0x19,0x0F,0x00,0x00},  // G
    {0x00,0x11,0x11,0x11,0x1F,0x11,0x11,0x11,0x00,0x00},  // H
    {0x00,0x1F,0x04,0x04,0x04,0x04,0x04,0x1F,0x00,0x00},  // I
    {0x00,0x0E,0x02,0x02,0x02,0x02,0x12,0x0C,0x00,0x00},  // J
    {0x00,0x11,0x12,0x14,0x18,0x14,0x12,0x11,0x00,0x00},  // K
    {0x00,0x10,0x10,0x10,0x10,0x10,0x10,0x1F,0x00,0x00},  // L
    {0x00,0x11,0x1B,0x1B,0x15,0x11,0x11,0x11,0x00,0x00},  // M
    {0x00,0x11,0x19,0x19,0x15,0x13,0x13,0x11,0x00,0x00},  // N
    {0x00,0x0E,0x11,0x11,0x11,0x11,0x11,0x0E,0x00,0x00},  // O
    {0x00,0x1E,0x11,0x11,0x1E,0x10,0x10,0x10,0x00,0x00},  // P
    {0x00,0x0E,0x11,0x11,0x11,0x11,0x11,0x0E,0x03,0x00},  // Q
    {0x00,0x1E,0x11,0x11,0x1E,0x13,0x11,0x10,0x00,0x00},  // R
    {0x00,0x0E,0x11,0x10,0x0E,0x01,0x11,0x0E,0x00,0x00},  // S
    {0x00,0x1F,0x04,0x04,0x04,0x04,0x04,0x04,0x00,0x00},  // T
    {0x00,0x11,0x11,0x11,0x11,0x11,0x11,0x0E,0x00,0x00},  // U
    {0x00,0x11,0x11,0x0A,0x0A,0x0A,0x04,0x04,0x00,0x00},  // V
    {0x00,0x21,0x2D,0x2D,0x1E,0x12,0x12,0x12,0x00,0x00},  // W
    {0x00,0x11,0x0A,0x0A,0x04,0x0A,0x0A,0x11,0x00,0x00},  // X
    {0x00,0x11,0x0A,0x0A,0x04,0x04,0x04,0x04,0x00,0x00},  // Y
    {0x00,0x1F,0x02,0x02,0x04,0x08,0x08,0x1F,0x00,0x00},  // Z
    {0x0C,0x08,0x08,0x08,0x08,0x08,0x08,0x08,0x0C,0x00},  // [
    {0x00,0x10,0x08,0x08,0x04,0x04,0x02,0x02,0x01,0x00},  // backslash
    {0x0C,0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x0C,0x00},  // ]
    {0x00,0x08,0x14,0x22,0x00,0x00,0x00,0x00,0x00,0x00},  // ^
    {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x3F},  // _
    {0x10,0x08,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},  // `
    {0x00,0x00,0x00,0x1E,0x01,0x0F,0x11,0x1F,0x00,0x00},  // a
    {0x10,0x10,0x10,0x1E,0x11,0x11,0x11,0x1E,0x00,0x00},  // b
    {0x00,0x00,0x00,0x0E,0x10,0x10,0x10,0x0E,0x00,0x00},  // c
    {0x01,0x01,0x01,0x0F,0x11,0x11,0x11,0x0F,0x00,0x00},  // d
    {0x00,0x00,0x00,0x0E,0x11,0x1F,0x10,0x0F,0x00,0x00},  // e
    {0x06,0x08,0x08,0x1E,0x08,0x08,0x08,0x08,0x00,0x00},  // f
    {0x00,0x00,0x00,0x0F,0x11,0x11,0x11,0x0F,0x01,0x0E},  // g
    {0x10,0x10,0x10,0x16,0x19,0x11,0x11,0x11,0x00,0x00},  // h
    {0x04,0x00,0x00,0x0C,0x04,0x04,0x04,0x1F,0x00,0x00},  // i
    {0x04,0x00,0x00,0x1C,0x04,0x04,0x04,0x04,0x04,0x18},  // j
    {0x10,0x10,0x10,0x12,0x14,0x1C,0x12,0x11,0x00,0x00},  // k
    {0x38,0x08,0x08,0x08,0x08,0x08,0x08,0x06,0x00,0x00},  // l
    {0x00,0x00,0x00,0x1F,0x15,0x15,0x15,0x15,0x00,0x00},  // m
    {0x00,0x00,0x00,0x16,0x19,0x11,0x11,0x11,0x00,0x00},  // n
    {0x00,0x00,0x00,0x0E,0x11,0x11,0x11,0x0E,0x00,0x00},  // o
    {0x00,0x00,0x00,0x1E,0x11,0x11,0x11,0x1E,0x10,0x10},  // p
    {0x00,0x00,0x00,0x0F,0x11,0x11,0x11,0x0F,0x01,0x01},  // q
    {0x00,0x00,0x00,0x0F,0x09,0x08,0x08,0x08,0x00,0x00},  // r
    {0x00,0x00,0x00,0x0F,0x10,0x0F,0x01,0x1E,0x00,0x00},  // s
    {0x00,0x08,0x08,0x1E,0x08,0x08,0x08,0x0E,0x00,0x00},  // t
    {0x00,0x00,0x00,0x11,0x11,0x11,0x11,0x0F,0x00,0x00},  // u
    {0x00,0x00,0x00,0x11,0x0A,0x0A,0x0A,0x04,0x00,0x00},  // v
    {0x00,0x00,0x00,0x11,0x15,0x0A,0x0A,0x0A,0x00,0x00},  // w
    {0x00,0x00,0x00,0x1B,0x0A,0x04,0x0A,0x1B,0x00,0x00},  // x
    {0x00,0x00,0x00,0x11,0x0A,0x0A,0x04,0x04,0x04,0x18},  // y
    {0x00,0x00,0x00,0x1F,0x02,0x04,0x08,0x1F,0x00,0x00},  // z
    {0x06,0x04,0x04,0x04,0x18,0x04,0x04,0x04,0x06,0x00},  // {
    {0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x04},  // |
    {0x0C,0x04,0x04,0x04,0x03,0x04,0x04,0x04,0x0C,0x00},  // }
    {0x00,0x00,0x00,0x00,0x1C,0x03,0x00,0x00,0x00,0x00},  // ~
};


static s32 isqrt32(u32 v) {
    u32 r = 0, b = 1u << 30;
    while (b > v) b >>= 2;
    while (b) {
        if (v >= r + b) { v -= r + b; r = (r >> 1) + b; }
        else r >>= 1;
        b >>= 2;
    }
    return (s32)r;
}

static void clearScreen(u16 *s, u16 c) {
    for (int i = 0; i < VW * VH; i++) s[i] = c;
}

static void rect(u16 *s, int x, int y, int w, int h, u16 c) {
    if (x < 0) { w += x; x = 0; }
    if (y < 0) { h += y; y = 0; }
    if (x + w > VW) w = VW - x;
    if (y + h > VH) h = VH - y;
    if (w <= 0 || h <= 0) return;
    for (int j = 0; j < h; j++) {
        u16 *p = s + (y + j) * VW + x;
        for (int i = 0; i < w; i++) p[i] = c;
    }
}

// rectangulo con las esquinas cortadas (1 px)
static void pill(u16 *s, int x, int y, int w, int h, u16 c) {
    rect(s, x + 1, y, w - 2, h, c);
    rect(s, x, y + 1, w, h - 2, c);
}

static int textW(const char *t, int sc) { return (int)strlen(t) * FONT_W * sc; }

static void glyph(u16 *s, int x, int y, int ch, u16 c, int sc) {
    if (ch < 32 || ch > 126) ch = '?';
    if (x < 0 || y < 0 || x + FONT_W * sc > VW || y + FONT_H * sc > VH) return;
    const u8 *g = font6[ch - 32];
    for (int r = 0; r < FONT_H; r++) {
        u8 bits = g[r];
        if (!bits) continue;
        for (int k = 0; k < FONT_W; k++) {
            if (!(bits & (0x20 >> k))) continue;
            if (sc == 1) s[(y + r) * VW + x + k] = c;
            else         rect(s, x + k * sc, y + r * sc, sc, sc, c);
        }
    }
}

static void text(u16 *s, int x, int y, const char *t, u16 c, int sc) {
    for (; *t; t++, x += FONT_W * sc) glyph(s, x, y, (unsigned char)*t, c, sc);
}

// tecla en naranja + descripcion en gris; avanza x
static void keyHint(int *x, int y, const char *key, const char *label) {
    text(fbTop, *x, y, key, C_ORG, 1);
    *x += textW(key, 1) + 4;
    text(fbTop, *x, y, label, C_GRAY, 1);
    *x += textW(label, 1) + 10;
}

static void drawHeader(const char *a, const char *b, u16 ca) {
    rect(fbTop, 0, 0, VW, 16, C_PANEL);
    rect(fbTop, 0, 0, 4, 16, C_ORG);
    text(fbTop, 10, 3, a, ca, 1);
    if (b) text(fbTop, 10 + textW(a, 1) + 8, 3, b, C_LGRAY, 1);
}

// pantallas de carga / error (arriba)
static void drawLoadScreen(const char *name) {
    clearScreen(fbTop, C_BG);
    drawHeader("CARGANDO", NULL, C_YEL);
    char t[36];
    snprintf(t, sizeof t, "%.34s", name);
    text(fbTop, 8, 40, t, C_WHITE, 1);
    rect(fbTop, 8, 62, 240, 8, C_PANEL2);
}

static void drawLoadBar(int pct) {
    if (pct < 0) pct = 0;
    if (pct > 100) pct = 100;
    rect(fbTop, 8, 62, 240 * pct / 100, 8, C_ORG);
    char t[8];
    snprintf(t, sizeof t, "%3d%%", pct);
    rect(fbTop, 8, 76, 40, 10, C_BG);
    text(fbTop, 8, 76, t, C_YEL, 1);
}

static void drawLoadNote(const char *note) {
    rect(fbTop, 8, 92, 240, 10, C_BG);
    text(fbTop, 8, 92, note, C_GRAY, 1);
}

static void drawErrorScreen(const char *msg) {
    clearScreen(fbTop, C_BG);
    drawHeader("ERROR", NULL, C_ORG);
    char t[38];
    snprintf(t, sizeof t, "%.36s", msg);
    text(fbTop, 8, 40, t, C_WHITE, 1);
    int x = 8;
    keyHint(&x, 176, "A", "volver");
}

// ---------------------------------------------------------------- reverb (Schroeder: 4 combs + 2 allpass)
typedef struct { s16 *buf; u32 len, idx; s32 lp; } Comb;
static s16 cb0[1789], cb1[1999], cb2[2237], cb3[2459], ab0[557], ab1[421], ab2[509], ab3[379];
static Comb combs[4] = { { cb0, 1789, 0, 0 }, { cb1, 1999, 0, 0 }, { cb2, 2237, 0, 0 }, { cb3, 2459, 0, 0 } };
static Comb aps[2]   = { { ab0, 557, 0, 0 }, { ab1, 421, 0, 0 } };
static Comb apsR[2]  = { { ab2, 509, 0, 0 }, { ab3, 379, 0, 0 } };
static s32 revMix = 51, revFb = 220, revDamp = 80;      // Q8

static void updateReverb(void) {
    revMix = revMixPct * 256 / 100;
    revFb  = 179 + decayPct * 69 / 100;                  // 0.70 .. 0.97
}

static s32 apRun(Comb *a, s32 w) {                       // difusion (allpass)
    s32 z = a->buf[a->idx];
    s32 v = clamp16(w + (z >> 1));
    a->buf[a->idx] = (s16)v;
    if (++a->idx >= a->len) a->idx = 0;
    return z - (v >> 1);
}

// entrada mono (suma de L y R); los 4 combs se mezclan con signos distintos para cada oido,
// asi la cola sale ancha y descorrelacionada
static void reverbProcess(s32 inL, s32 inR, s32 *wl, s32 *wr) {
    s32 x = (((inL + inR) >> 1) * (256 - revFb)) >> 8;   // compensa la ganancia de la realimentacion
    s32 y[4];
    for (int i = 0; i < 4; i++) {
        Comb *c = &combs[i];
        y[i] = c->buf[c->idx];
        c->lp += ((y[i] - c->lp) * revDamp) >> 8;        // amortiguacion: la cola se oscurece
        c->buf[c->idx] = (s16)clamp16(x + ((c->lp * revFb) >> 8));
        if (++c->idx >= c->len) c->idx = 0;
    }
    s32 l = (y[0] - y[1] + y[2] - y[3]) >> 2;
    s32 r = (y[0] + y[1] - y[2] - y[3]) >> 2;
    l = apRun(&aps[1], apRun(&aps[0], l));
    r = apRun(&apsR[1], apRun(&apsR[0], r));
    *wl = l; *wr = r;
}

// ---------------------------------------------------------------- motor
// Volumen automatico: el sample ya esta normalizado por su pico, pero la musica real tiene
// mucho mas pico que promedio y suena bajito. Medimos el RMS y subimos hasta ~-9 dBFS
// (maximo +16 dB); el limitador suave de la salida se encarga de los picos.
static void computeAuto(void) {
    u64 sum = 0;
    u32 n = 0, step = srcLen > 200000 ? 4 : 1;
    for (u32 i = 0; i < srcLen; i += step) { s32 v = src[i]; sum += (u32)(v * v); n++; }
    s32 rms = n ? isqrt32((u32)(sum / n)) : 1;
    if (rms < 1) rms = 1;
    s32 q = 44 * 256 / rms;
    if (q < 256) q = 256;
    if (q > 1664) q = 1664;
    autoQ = q;
}

static void updateInc(void) {
    gainC = (gain * autoQ) >> 8;
    gainT = (((gain * 2) / 5) * autoQ) >> 8;
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

// ---- estereo, shimmer y filtro
static s32 panTab[33];                        // ganancias Q8 de potencia constante (centro = 256 en cada oido)
static s32 shimRatio[4];                      // razones Q16 de +12, +24, +19 y -12 semitonos
static s32 aTab[128], fcHz[128];              // coeficiente (Q15) y frecuencia del filtro por paso
static s32 fS[2][2];                          // estados del filtro (L, R) de 2 polos
static s32 aCur = 32768, aTgt = 32768;
static u32 lfoPh = 0, shPh = 0;               // fases: barrido del filtro (~12 s) y fundido del shimmer (~17 s)
static u32 fCnt = 0;
#define LFO_INC   10938u                      // 2^32 / (12 s * 32728.5 Hz)
#define SHIM_INC  7720u                       // 2^32 / (17 s * 32728.5 Hz)

static void initTables(void) {
    for (int i = 0; i <= 32; i++) panTab[i] = (s32)(362.0f * cosf((float)i * 3.14159265f / 64.0f));
    shimRatio[0] = (s32)(65536.0f * exp2f(12.0f / 12.0f));
    shimRatio[1] = (s32)(65536.0f * exp2f(24.0f / 12.0f));
    shimRatio[2] = (s32)(65536.0f * exp2f(19.0f / 12.0f));
    shimRatio[3] = (s32)(65536.0f * exp2f(-12.0f / 12.0f));
    for (int c = 0; c < 128; c++) {
        float fc = 40.0f * exp2f((float)c * 7.81f / 127.0f);       // 40 Hz .. ~9 kHz
        float a = 1.0f - expf(-6.2831853f * fc / 32728.5f);
        fcHz[c] = (s32)fc;
        aTab[c] = (s32)(32768.0f * a);
    }
}

// triangulo suavizado 0..256 a partir de una fase de 32 bit
static s32 smooth01(u32 ph) {
    u32 t = ph < 0x80000000u ? ph : ~ph;
    s32 x = (s32)(t >> 16);
    if (x > 32767) x = 32767;
    s32 x2 = (x * x) >> 15;
    s32 v = 3 * x2 - ((2 * x2 * x) >> 15);
    return v >> 7;
}

static void filterTarget(void) {
    if (filtPct >= 100 && !sweepPct) { aTgt = 32768; return; }
    s32 c = filtPct * 127 / 100;
    if (sweepPct) c -= sweepPct * smooth01(lfoPh) / 256;       // el barrido baja el corte desde el valor fijado
    aTgt = aTab[clampi(c, 0, 127)];
}

static inline s32 lp2(s32 *st, s32 x) {
    st[0] += (((x - st[0]) >> 3) * aCur) >> 12;
    st[1] += (((st[0] - st[1]) >> 3) * aCur) >> 12;
    return st[1];
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
        s32 inc = (s32)inc16, amp = 256;
        bool shim = false;
        if (shimPct) {                                            // shimmer: octavas que suben y bajan de a poco
            s32 env = smooth01(shPh);
            if ((s32)(rnd() % 100) < shimPct * env / 256) {
                u32 r = rnd() % 100;
                inc = (s32)(((u64)(u32)inc * (u32)shimRatio[r < 55 ? 0 : (r < 80 ? 1 : (r < 92 ? 2 : 3))]) >> 16);
                amp = 64 + env * 192 / 256;
                shim = true;
            }
        }
        if (!shim && harmPct && (rnd() % 100) < (u32)harmPct)     // armonia: grano transpuesto
            inc = (s32)(((u64)(u32)inc * (u32)harmRatio[rnd() & 3]) >> 16);
        if (jitterC) {                                            // desafinacion aleatoria en cents
            s32 j = (s32)(rnd() % (u32)(2 * jitterC + 1)) - jitterC;
            inc += (inc * j) / 1731;
        }
        u32 len = (u32)(sizeMs * OUT_RATE / 1000);
        if (shim) len += len >> 1;                                // los granos shimmer son mas largos
        if (revPct && (rnd() % 100) < (u32)revPct) {              // grano al reves: parte del final
            start += (s32)(((len >> 4) * ((u32)inc >> 4)) >> 8);
            inc = -inc;
        }
        start = clampi(start, 0, (s32)srcLen - 2);
        s32 span = panPct * 16 / 100;                             // panorama: posicion 0..32, centro 16
        s32 pp = 16 + (s32)(rnd() % (u32)(2 * span + 1)) - span;
        grains[g].ipos = (u32)start;
        grains[g].fpos = 0;
        grains[g].inc  = inc;
        grains[g].wpos = 0;
        grains[g].winc = ((u32)WIN_LEN << 16) / len;
        grains[g].pl   = panTab[pp];
        grains[g].pr   = panTab[32 - pp];
        grains[g].amp  = amp;
        grains[g].shim = shim;
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
#define SCALE(v) ((((v) * normQ >> 8) * gainC) >> 4)

static void render(s16 *dstL, s16 *dstR, int n) {
    for (int i = 0; i < n; i++) {
        if (recording) { dstL[i] = 0; dstR[i] = 0; continue; }
        lfoPh += LFO_INC;
        shPh  += SHIM_INC;
        if ((++fCnt & 31) == 0) filterTarget();
        aCur += (aTgt - aCur) >> 6;

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

        // nube de granos: directo (dL, dR) y envio a la reverb (sL, sR)
        s32 dL = 0, dR = 0, sL = 0, sR = 0;
        if (mixQ < MIX_FULL) {
            if (playing && !touching && !freezeKey) advancePos();
            if (playing || touching) {
                if (--untilSpawn <= 0) { spawn(); untilSpawn = OUT_RATE / density; }
            }
            s32 aL = 0, aR = 0, zL = 0, zR = 0;
            for (int g = 0; g < MAX_GRAINS; g++) {
                Grain *gr = &grains[g];
                if (!gr->on) continue;
                u32 si = gr->ipos;
                if (si >= srcLen - 1 || gr->wpos >= ((u32)WIN_LEN << 16)) { gr->on = false; continue; }
                s32 a = src[si], b = src[si + 1];
                s32 s = a + (((b - a) * (gr->fpos >> 8)) >> 8);        // interpolacion lineal
                u32 wi = gr->wpos >> 16;
                s32 w = win[wi] + (((win[wi + 1] - win[wi]) * (s32)((gr->wpos >> 8) & 0xFF)) >> 8);
                s32 v = (((s * w) >> 7) * gr->amp) >> 8;                // s8 -> s16 con ventana Q15
                s32 vl = (v * gr->pl) >> 8, vr = (v * gr->pr) >> 8;
                if (gr->shim) { zL += vl; zR += vr; } else { aL += vl; aR += vr; }
                s32 f = gr->fpos + gr->inc;
                gr->ipos += (u32)(f >> 16);
                gr->fpos  = f & 0xFFFF;
                gr->wpos += gr->winc;
            }
            // el shimmer se oye poco directo y mucho dentro de la reverb
            dL = softClip(SCALE(aL + ((zL * 90) >> 8)));
            dR = softClip(SCALE(aR + ((zR * 90) >> 8)));
            sL = softClip(SCALE(aL + zL + (zL >> 1)));
            sR = softClip(SCALE(aR + zR + (zR >> 1)));
        }

        // reverb estereo sobre la nube; el fundido la apaga junto con ella
        s32 wl, wr;
        reverbProcess(sL, sR, &wl, &wr);
        s32 fadeG = 32768 - (mixQ >> 9);
        s32 cmL = (((dL * (256 - (revMix >> 1)) + wl * revMix) >> 8) * fadeG) >> 15;
        s32 cmR = (((dR * (256 - (revMix >> 1)) + wr * revMix) >> 8) * fadeG) >> 15;

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
                    s32 x = ((s * 256 * gainT) >> 4);
                    tr = (x * (trackGate >> 3)) >> 12;
                    tr = (tr * (mixQ >> 9)) >> 15;                      // el fundido sube el track mientras baja la nube
                    trackF += (s32)cleanInc;
                    trackI += trackF >> 16;
                    trackF &= 0xFFFF;
                }
            }
        }

        // filtro pasa-bajos de toda la salida (con el filtro abierto solo sigue la senal, sin gastar)
        s32 oL = cmL + tr, oR = cmR + tr;
        if (aCur >= 32700 && aTgt >= 32768) {
            fS[0][0] = fS[0][1] = oL;
            fS[1][0] = fS[1][1] = oR;
        } else {
            oL = lp2(fS[0], oL);
            oR = lp2(fS[1], oR);
        }
        dstL[i] = (s16)clamp16(softClip(oL));                   // limitador suave en la salida
        dstR[i] = (s16)clamp16(softClip(oR));
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
    computeAuto();
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
    computeAuto();
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
                m = ((s32)p[0] - 128) * 256;
                if (ch == 2) m = (m + ((s32)p[1] - 128) * 256) >> 1;
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
        if ((++nb & 31) == 0) drawLoadBar((int)(done / (frames / 100 + 1)));
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
    computeAuto();
    updateInc();
    resetTransport(false, false);                           // los tracks cargan en pausa, al inicio
    computePeaks();

    drawLoadBar(100);
    drawLoadNote("guardando cache...");
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

#define BR_ROWS 14

static void drawBrowser(void) {
    clearScreen(fbTop, C_BG);
    char cwd[256], t[40];
    if (!getcwd(cwd, sizeof(cwd))) strcpy(cwd, "?");
    snprintf(t, sizeof t, "%.34s", cwd);
    drawHeader("SD", t, C_ORG);
    if (nEnt == 0) text(fbTop, 8, 24, "(sin .wav ni carpetas)", C_GRAY, 1);
    for (int r = 0; r < BR_ROWS; r++) {
        int i = scrollTop + r;
        if (i >= nEnt) break;
        int y = 21 + r * 11;
        bool sl = (i == sel);
        if (sl) rect(fbTop, 0, y, VW - 8, 11, C_YEL);
        char n[40];
        if (ents[i].dir) snprintf(n, sizeof n, "[%.34s]", ents[i].name);
        else             snprintf(n, sizeof n, "%.36s", ents[i].name);
        text(fbTop, 8, y + 1, n, sl ? C_DARK : (ents[i].dir ? C_ORG : C_LGRAY), 1);
    }
    if (nEnt > BR_ROWS) {                                    // barra de scroll
        int full = BR_ROWS * 11;
        int th = full * BR_ROWS / nEnt;
        if (th < 6) th = 6;
        int ty = 21 + (full - th) * scrollTop / (nEnt - BR_ROWS);
        rect(fbTop, 250, 21, 3, full, C_PANEL2);
        rect(fbTop, 250, ty, 3, th, C_ORG);
    }
    int x = 8;
    keyHint(&x, 178, "A", "abrir");
    keyHint(&x, 178, "B", "volver");
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
enum { P_SPEED, P_PITCH, P_SIZE, P_DENS, P_SPRAY, P_DRIFT, P_HARM, P_SHIM, P_JIT, P_REV, P_PAN,
       P_REVERB, P_DECAY, P_FILT, P_SWEEP, P_VOL, P_FADE, P_DROPFROM, P_LOAD, P_REC, P_COUNT };
static const char *const pLabel[P_COUNT] = {
    "VELOCID", "PITCH", "TAMANO", "DENSID", "SPRAY", "DERIVA", "ARMONIA", "SHIMMER", "JITTER", "REVERSA", "ESTEREO",
    "REVERB", "COLA", "FILTRO", "BARRIDO", "VOLUMEN", "FUNDIDO", "DROP DE", "CARGAR", "MIC REC"
};
static int cur = 0, pTop = 0;
#define P_ROWS 9

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
        case P_SHIM:  shimPct  = clampi(shimPct + d * 5, 0, 100);     break;
        case P_PAN:   panPct   = clampi(panPct + d * 5, 0, 100);      break;
        case P_FILT:  filtPct  = clampi(filtPct + d * 4, 0, 100);     break;
        case P_SWEEP: sweepPct = clampi(sweepPct + d * 5, 0, 100);    break;
        case P_JIT:   jitterC  = clampi(jitterC + d * 5, 0, 100);     break;
        case P_REV:   revPct   = clampi(revPct + d * 10, 0, 100);     break;
        case P_REVERB: revMixPct = clampi(revMixPct + d * 5, 0, 100); updateReverb(); break;
        case P_DECAY: decayPct = clampi(decayPct + d * 5, 0, 100);    updateReverb(); break;
        case P_VOL:   gain     = clampi(gain + d * 4, 4, 128);        updateInc(); break;
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
        case P_SHIM:  snprintf(b, n, "%ld%%", (long)shimPct); break;
        case P_PAN:   snprintf(b, n, "%ld%%", (long)panPct); break;
        case P_FILT:
            if (filtPct >= 100) snprintf(b, n, "abierto");
            else                snprintf(b, n, "%ld Hz", (long)fcHz[filtPct * 127 / 100]);
            break;
        case P_SWEEP:
            if (sweepPct) snprintf(b, n, "%ld%%", (long)sweepPct);
            else          snprintf(b, n, "off");
            break;
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

// 0..256 para la barra de cada parametro (-1 = sin barra)
static s32 paramFrac(int i) {
    switch (i) {
        case P_SPEED:  return (speedPct + 200) * 256 / 400;
        case P_PITCH:  return (semis + 24) * 256 / 48;
        case P_SIZE:   return isqrt32((u32)sizeMs * 65536u / 2000u);
        case P_DENS:   return density * 256 / 100;
        case P_SPRAY:  return sprayMs * 256 / 500;
        case P_DRIFT:  return driftPct * 256 / 100;
        case P_HARM:   return harmPct * 256 / 100;
        case P_SHIM:   return shimPct * 256 / 100;
        case P_PAN:    return panPct * 256 / 100;
        case P_FILT:   return filtPct * 256 / 100;
        case P_SWEEP:  return sweepPct * 256 / 100;
        case P_JIT:    return jitterC * 256 / 100;
        case P_REV:    return revPct * 256 / 100;
        case P_REVERB: return revMixPct * 256 / 100;
        case P_DECAY:  return decayPct * 256 / 100;
        case P_VOL:    return gain * 256 / 128;
        case P_FADE:   return fadeIdx * 256 / 7;
        default:       return -1;
    }
}

#define PR_Y0  64
#define PR_H   11

static char sigCache[16][128];
static bool topFull = true;

// true si lo que va en ese bloque cambio desde la ultima vez (asi solo se redibuja lo necesario)
static bool sigChanged(int slot, const char *sig) {
    if (!topFull && !strcmp(sigCache[slot], sig)) return false;
    strncpy(sigCache[slot], sig, sizeof(sigCache[slot]) - 1);
    sigCache[slot][sizeof(sigCache[slot]) - 1] = 0;
    return true;
}

static void drawParamRow(int r, int i, const char *v, int up, int dn) {
    int y = PR_Y0 + r * PR_H;
    bool sl = (i == cur);
    rect(fbTop, 0, y, VW, PR_H, sl ? C_YEL : C_BG);
    text(fbTop, 8, y + 1, pLabel[i], sl ? C_DARK : C_LGRAY, 1);
    s32 f = paramFrac(i);
    if (f >= 0) {
        int bx = 66, bw = 84;
        u16 fc = sl ? C_ORG : C_GRAY;
        int fw = (int)f * bw / 256;
        rect(fbTop, bx, y + 3, bw, 5, sl ? C_YELD : C_PANEL2);
        if (i == P_SPEED || i == P_PITCH) {                  // barras bipolares: parten del centro
            int cx = bx + bw / 2;
            if (fw >= bw / 2) rect(fbTop, cx, y + 3, fw - bw / 2, 5, fc);
            else              rect(fbTop, bx + fw, y + 3, bw / 2 - fw, 5, fc);
            rect(fbTop, cx, y + 2, 1, 7, sl ? C_DARK : C_LGRAY);
        } else {
            rect(fbTop, bx, y + 3, fw, 5, fc);
        }
    }
    text(fbTop, 240 - textW(v, 1), y + 1, v, sl ? C_DARK : C_WHITE, 1);
    if (up) text(fbTop, 246, y + 1, "^", C_ORG, 1);
    if (dn) text(fbTop, 246, y + 1, "v", C_ORG, 1);
}

static void drawMain(s32 heardI) {
    if (topFull) clearScreen(fbTop, C_BG);
    char sig[128], a[20], b[20], v[24];

    // cabecera: titulo + estado
    const char *st = recording ? "REC" : (playing ? "PLAY" : "PAUSA");
    int dropSt = dropOn ? 2 : (mixQ > 0 ? 1 : 0);
    snprintf(sig, sizeof sig, "%s|%d|%d", st, dropSt, (int)sdOK);
    if (sigChanged(0, sig)) {
        rect(fbTop, 0, 0, VW, 16, C_PANEL);
        rect(fbTop, 0, 0, 4, 16, C_ORG);
        text(fbTop, 10, 3, "EFEES", C_WHITE, 1);
        text(fbTop, 46, 3, "granular", C_ORG, 1);
        if (!sdOK) text(fbTop, 100, 3, "sin SD", C_GRAY, 1);
        int w = textW(st, 1) + 10, x = VW - 6 - w;
        bool on = recording || playing;
        pill(fbTop, x, 2, w, 12, on ? C_ORG : C_PANEL2);
        text(fbTop, x + 5, 3, st, on ? C_DARK : C_LGRAY, 1);
        if (dropSt) {
            w = textW("DROP", 1) + 10;
            x -= w + 4;
            pill(fbTop, x, 2, w, 12, dropSt == 2 ? C_WHITE : C_YELD);
            text(fbTop, x + 5, 3, "DROP", C_DARK, 1);
        }
    }

    // nombre del archivo
    snprintf(sig, sizeof sig, "%.40s", curName);
    if (sigChanged(1, sig)) {
        rect(fbTop, 0, 18, VW, 11, C_BG);
        text(fbTop, 8, 19, sig, C_LGRAY, 1);
    }

    // tiempo grande + duracion + loop
    u32 now10 = (u32)heardI * 10 / srcRate, len10 = srcLen * 10 / srcRate;
    char lp[48];
    fmtT(a, sizeof a, now10);
    fmtT(b, sizeof b, len10);
    if (loopOn) {
        char l1[20], l2[20];
        fmtT(l1, sizeof l1, (u32)loopStart * 10 / srcRate);
        fmtT(l2, sizeof l2, (u32)loopEnd * 10 / srcRate);
        snprintf(lp, sizeof lp, "LOOP %s-%s", l1, l2);
    } else {
        snprintf(lp, sizeof lp, "loop off");
    }
    snprintf(sig, sizeof sig, "%s|%s|%lu|%s", a, b, (unsigned long)srcRate, lp);
    if (sigChanged(2, sig)) {
        rect(fbTop, 0, 30, VW, 22, C_BG);
        text(fbTop, 8, 31, a, C_YEL, 2);
        char d[24], r[16];
        snprintf(d, sizeof d, "/ %s", b);
        snprintf(r, sizeof r, "%luHz", (unsigned long)srcRate);
        text(fbTop, 8 + textW(a, 2) + 6, 41, d, C_GRAY, 1);
        text(fbTop, VW - 8 - textW(r, 1), 33, r, C_GRAY, 1);
        text(fbTop, VW - 8 - textW(lp, 1), 43, lp, loopOn ? C_YEL : C_GRAY, 1);
    }

    // barra de progreso
    int pxp = (int)((u32)heardI * 240 / srcLen);
    int l0 = (int)((u32)loopStart * 240 / srcLen), l1 = (int)((u32)loopEnd * 240 / srcLen);
    snprintf(sig, sizeof sig, "%d|%d|%d|%d|%d", pxp, (int)loopOn, l0, l1, (int)dropOn);
    if (sigChanged(3, sig)) {
        rect(fbTop, 0, 52, VW, 8, C_BG);
        rect(fbTop, 8, 54, 240, 4, C_PANEL2);
        if (loopOn) rect(fbTop, 8 + l0, 54, l1 - l0 + 1, 4, C_YELD);
        rect(fbTop, 8, 54, pxp, 4, dropOn ? C_WHITE : C_ORG);
        rect(fbTop, 8 + pxp, 52, 2, 8, C_WHITE);
    }

    // parametros (con scroll)
    if (cur < pTop) pTop = cur;
    if (cur >= pTop + P_ROWS) pTop = cur - P_ROWS + 1;
    for (int r = 0; r < P_ROWS; r++) {
        int i = pTop + r;
        char sg[96];
        if (i >= P_COUNT) {
            if (sigChanged(4 + r, "-")) rect(fbTop, 0, PR_Y0 + r * PR_H, VW, PR_H, C_BG);
            continue;
        }
        valStr(i, v, sizeof v);
        int up = (r == 0 && pTop > 0), dn = (r == P_ROWS - 1 && pTop + P_ROWS < P_COUNT);
        snprintf(sg, sizeof sg, "%d|%d|%s|%d|%d|%d", i, (int)(i == cur), v, (int)paramFrac(i), up, dn);
        if (sigChanged(4 + r, sg)) drawParamRow(r, i, v, up, dn);
    }

    // ayuda (fija)
    if (topFull) {
        rect(fbTop, 8, 165, 240, 1, C_PANEL2);
        int x = 8;
        keyHint(&x, 169, "START", "play");
        keyHint(&x, 169, "A", "DROP");
        keyHint(&x, 169, "B", "freeze");
        x = 8;
        keyHint(&x, 180, "SELECT", "loop");
        keyHint(&x, 180, "X/Y", "in/out");
        keyHint(&x, 180, "L/R", "+-5s");
    }
    topFull = false;
}

// ---------------------------------------------------------------- vista (pantalla tactil)
#define WAVE_H  154                  // filas de la onda; debajo, la barra de botones
#define BAR_Y   156
#define MID     80
#define AMP     66
#define STRIP   7                    // filas de arriba reservadas a los granos (la onda nunca llega ahi)

#define C_SPRAY    RGB8( 46,  46,  52)
#define C_LOOPBG   RGB8( 54,  48,  30)
#define C_LOOPSPR  RGB8( 68,  60,  36)
#define C_AXIS     RGB8( 52,  52,  58)

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
    if (x == v->cx) {                                        // cabeza: naranja (blanca en DROP)
        u16 cc = v->drop ? C_WHITE : C_ORG;
        for (int y = 0; y < WAVE_H; y++, p += VW) *p = cc;
        return;
    }
    bool inLoop  = v->lon && x >= v->ls && x <= v->le;
    bool inSpray = x >= v->cx - v->spr && x <= v->cx + v->spr;
    u16 bg = inLoop ? (inSpray ? C_LOOPSPR : C_LOOPBG) : (inSpray ? C_SPRAY : C_BG);
    if (v->lon && (x == v->ls || x == v->le)) bg = C_YEL;
    // gris = por tocar, amarillo claro = ya sonado, blanco = ancho de un grano
    u16 wv = (x >= v->cx && x < v->cx + v->gw) ? C_WHITE : (x < v->cx ? C_YEL : C_GRAY);
    for (int y = 0; y < WAVE_H; y++, p += VW)
        *p = (y >= waveA[x] && y <= waveB[x]) ? wv : (y == MID ? C_AXIS : bg);
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
        u16 c = (x == v->cx) ? (v->drop ? C_WHITE : C_ORG)
              : inLoop ? (inSpray ? C_LOOPSPR : C_LOOPBG)
              : (inSpray ? C_SPRAY : C_BG);
        u16 *p = fb + x;
        for (int y = 0; y < STRIP; y++, p += VW) *p = c;
    }
    for (int g = 0; g < MAX_GRAINS; g++) {                   // marcas de los granos sonando
        if (!grains[g].on || grains[g].ipos >= srcLen) continue;
        int gx = (int)(grains[g].ipos * 256 / srcLen);
        u16 *p = fb + gx;
        for (int y = 0; y < STRIP - 1; y++, p += VW) *p = C_YEL;
    }
}

// triangulo relleno apuntando a la derecha (dir=+1) o a la izquierda (dir=-1), 14 filas
static void fillTri(int x, int y, int dir, u16 c) {
    for (int r = 0; r < 14; r++) {
        int w = (r < 7 ? r + 1 : 14 - r) * 2;
        if (dir > 0) rect(fb, x, y + r, w, 1, c);
        else         rect(fb, x - w, y + r, w, 1, c);
    }
}

#define BTN_Y  159
#define BTN_H  30
#define BTN_W  46

static void btnFrame(int x, u16 bg) { pill(fb, x, BTN_Y, BTN_W, BTN_H, bg); }
static void btnLabel(int x, const char *t, u16 c) { text(fb, x + (BTN_W - textW(t, 1)) / 2, 177, t, c, 1); }

// 5 botones de 46 px, paso 50: x = 4, 54, 104, 154, 204. Cortes del toque en main: 52, 102, 152, 202.
static void drawButtons(void) {
    rect(fb, 0, WAVE_H, VW, VH - WAVE_H, C_PANEL);
    rect(fb, 0, WAVE_H, VW, 1, C_LINE);
    int x, cx, iy = 162;
    u16 fg;

    // [play / pausa]
    x = 4; cx = x + 23;
    fg = playing ? C_DARK : C_LGRAY;
    btnFrame(x, playing ? C_ORG : C_PANEL2);
    if (playing) { rect(fb, cx - 8, iy, 5, 14, fg); rect(fb, cx + 3, iy, 5, 14, fg); }
    else         { fillTri(cx - 6, iy, +1, fg); }
    btnLabel(x, playing ? "PAUSA" : "PLAY", fg);

    // [loop]: corchetes
    x = 54; cx = x + 23;
    fg = loopOn ? C_DARK : C_LGRAY;
    btnFrame(x, loopOn ? C_YEL : C_PANEL2);
    rect(fb, cx - 14, iy, 3, 14, fg); rect(fb, cx - 14, iy, 6, 3, fg); rect(fb, cx - 14, iy + 11, 6, 3, fg);
    rect(fb, cx + 11, iy, 3, 14, fg); rect(fb, cx + 8, iy, 6, 3, fg);  rect(fb, cx + 8, iy + 11, 6, 3, fg);
    rect(fb, cx - 3, iy + 5, 6, 4, fg);
    btnLabel(x, "LOOP", fg);

    // [al inicio]: barra + triangulo a la izquierda
    x = 104; cx = x + 23;
    fg = C_LGRAY;
    btnFrame(x, C_PANEL2);
    rect(fb, cx - 12, iy, 3, 14, fg);
    fillTri(cx + 8, iy, -1, fg);
    btnLabel(x, "INICIO", fg);

    // [carpeta]: abre el navegador de la SD
    x = 154; cx = x + 23;
    fg = C_LGRAY;
    btnFrame(x, C_PANEL2);
    rect(fb, cx - 12, iy + 1, 9, 3, fg);
    rect(fb, cx - 12, iy + 4, 24, 10, fg);
    btnLabel(x, "SD", fg);

    // [DROP]: flecha hacia abajo
    x = 204; cx = x + 23;
    fg = dropOn ? C_ORG : C_LGRAY;
    btnFrame(x, dropOn ? C_WHITE : C_PANEL2);
    rect(fb, cx - 3, iy, 6, 7, fg);
    for (int r = 0; r < 8; r++) rect(fb, cx - 8 + r, iy + 6 + r, 16 - 2 * r, 1, fg);
    btnLabel(x, "DROP", dropOn ? C_DARK : fg);

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

// ---------------------------------------------------------------- anillo de audio
// El indice de escritura siempre queda alineado a CHUNK (si no, el ultimo bloque de cada vuelta
// se sale del buffer y deja un hueco con audio viejo).
static inline u32 ringSync(u32 ph) { return (ph + LEAD) & ~(u32)(CHUNK - 1) & (OUT_LEN - 1); }

// adelanto de escritura sobre el playhead, en ticks del timer (16 por muestra) y con signo:
// al contar los ticks que pasaron entre cuadros, un tiron largo se detecta (leadT < 0) aunque
// el indice del anillo ya haya dado la vuelta
static s32 leadT = LEAD * 16;
static u32 tPrev = 0, ringResyncs = 0;

static void ringReset(u32 *wr, u32 t) {
    u32 ph = (t >> 4) & (OUT_LEN - 1);
    *wr = ringSync(ph);
    leadT = (s32)(((*wr - ph) & (OUT_LEN - 1)) * 16);
    tPrev = t;
    ringResyncs++;
}

// renderiza por delante del playhead; si el playhead nos alcanzo (hubo un tiron) resincroniza
static u32 pump(u32 wr, u32 t) {
    leadT -= (s32)((t - tPrev) & 0xFFFF);
    tPrev = t;
    if (leadT < 0) ringReset(&wr, t);
    while (leadT < LEAD * 16) {
        render(&outL[wr], &outR[wr], CHUNK);
        DC_FlushRange(&outL[wr], CHUNK * 2);
        DC_FlushRange(&outR[wr], CHUNK * 2);
        wr = (wr + CHUNK) & (OUT_LEN - 1);
        leadT += CHUNK * 16;
    }
    return wr;
}

// ---------------------------------------------------------------- main
int main(void) {
    // las dos pantallas son bitmaps de 16 bit: arriba parametros, abajo forma de onda y botones
    videoSetMode(MODE_5_2D | DISPLAY_BG3_ACTIVE);
    videoSetModeSub(MODE_5_2D | DISPLAY_BG3_ACTIVE);
    vramSetBankA(VRAM_A_MAIN_BG);
    vramSetBankC(VRAM_C_SUB_BG);
    int bgMain = bgInit(3, BgType_Bmp16, BgSize_B16_256x256, 0, 0);
    int bgSub  = bgInitSub(3, BgType_Bmp16, BgSize_B16_256x256, 0, 0);
    fbTop = (u16 *)bgGetGfxPtr(bgMain);
    fb    = (u16 *)bgGetGfxPtr(bgSub);
    clearScreen(fbTop, C_BG);
    clearScreen(fb, C_BG);

    sdOK = fatInitDefault();
    soundEnable();

    for (int i = 0; i < OUT_LEN; i++) outL[i] = outR[i] = 0;
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
    initTables();
    computeAuto();
    updateReverb();
    updateInc();
    resetTransport(true, true);
    computePeaks();

    DC_FlushRange(outL, sizeof(outL));
    DC_FlushRange(outR, sizeof(outR));
    // dos canales mono, uno a cada lado: eso da el estereo
    soundPlaySample(outL, SoundFormat_16Bit, sizeof(outL), OUT_RATE, 127, 0, true, 0);
    soundPlaySample(outR, SoundFormat_16Bit, sizeof(outR), OUT_RATE, 127, 127, true, 0);

    // reloj del playhead: 33.514 MHz / 64 = 523656 Hz = 16 ticks por muestra de salida
    TIMER_DATA(0) = 0;
    TIMER_CR(0) = TIMER_ENABLE | TIMER_DIV_64;

    u32 wr = LEAD, frame = 0;
    tPrev = TIMER_DATA(0);
    leadT = LEAD * 16;
    bool uiDirty = true;
    keysSetRepeat(15, 3);

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
            if (sel >= scrollTop + BR_ROWS) scrollTop = sel - (BR_ROWS - 1);
            if (kd & KEY_B) { browsing = false; topFull = true; }
            else if ((kd & KEY_A) && nEnt > 0) {
                if (ents[sel].dir) {
                    if (chdir(ents[sel].name) == 0) scanDir();
                    dirty = true;
                } else {
                    // silenciamos el anillo: la carga tarda segundos y no renderizamos
                    playing = false;
                    for (int i = 0; i < OUT_LEN; i++) outL[i] = outR[i] = 0;
                    DC_FlushRange(outL, sizeof(outL));
    DC_FlushRange(outR, sizeof(outR));
                    drawLoadScreen(ents[sel].name);
                    const char *err = loadWav(ents[sel].name);
                    if (err) {
                        if (lostSample) useRec("[demo/mic]");   // la carga fallida nos dejo sin sample
                        drawErrorScreen(err);
                        while (1) { swiWaitForVBlank(); scanKeys(); if (keysDown() & (KEY_A | KEY_B)) break; }
                        dirty = true;
                    } else {
                        browsing = false;
                        topFull = true;
                    }
                    ringReset(&wr, TIMER_DATA(0));                // re-sincroniza con el playhead
                    fullRedraw = true;
                    uiDirty = true;
                }
            }
            if (dirty && browsing) drawBrowser();
        } else if (recording) {
            touching = false; freezeKey = false; touchDrag = false;
            if (micDone) { finishRec(); topFull = true; uiDirty = true; }
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
            if (kh & KEY_TOUCH) {
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

        // pantallas primero: justo despues del vblank no se ven cortes
        s32 lt = leadT - (s32)((TIMER_DATA(0) - tPrev) & 0xFFFF);
        u32 lead = lt > 0 ? (u32)lt / 16 : 0;
        s32 hp = heardPos(lead);
        updateView(hp);
        if (!browsing && (uiDirty || (++frame & 3) == 0)) { drawMain(hp); uiDirty = false; }

        // audio: renderiza por delante del playhead
        wr = pump(wr, TIMER_DATA(0));
    }
    return 0;
}
