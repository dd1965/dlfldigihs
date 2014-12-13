// ----------------------------------------------------------------------------
// tbchs.cxx  --  tbchs modem
//
// Copyright (C) 2006
//		Dave Freese, W1HKJ
//
// This file is part of fldigi.  Adapted from code contained in gMFSK source code
// distribution.
//  gMFSK Copyright (C) 2001, 2002, 2003
//  Tomi Manninen (oh2bns@sral.fi)
//
// Fldigi is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// Fldigi is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with fldigi.  If not, see <http://www.gnu.org/licenses/>.
// ----------------------------------------------------------------------------


#include <config.h>
#include <iostream>
#include <string>
#include <cstring>
//#include <algorithm>
#include <fstream>
using namespace std;

#include "tbchs.h"
#include "fl_digi.h"
#include "digiscope.h"
#include "misc.h"
#include "waterfall.h"
#include "confdialog.h"
#include "configuration.h"
#include "status.h"
#include "digiscope.h"
#include "trx.h"
#include "debug.h"
#include "synop.h"
#include "main.h"
#include "rs8.h"
#include "dl_fldigi/hbtint.h"

string crcstr ="1234";
string s = "PSB,0001,000000,0.0,0.0,0,0,0,0,107,26,7656";
 string comma = ",";
string asterisk ="*";
string dollar= "$$";
		   string lcallsign;
		   string sequence;
		   string ltime;
		   string latstring ;
		   string longstring;
		   string altitude ;
		   string speed;
		   string satno ;
		   string satfix ;
		   string insidetemp;
		   string outsidetemp;
		   string volts;   

uint8_t pkt[256];
char msg[80];

int dspcnt1 = 0;
char tbchsmsg[80];

static char payloadtxt[90];
static char payloadtxtfinal[100];
unsigned long long tag = (0xB74DB7DF8A532F3EULL);		//  correlation tag value  //This is reveresed order for bit by bit routine.
uint64_t ltemp1 = 0;                        // this one needs to be persistent
uint64_t ltemp2;

#define N 40   //Sample Rate / baud rate 48000/1200
float thetahi = 2.0f * M_PI * (2200) / tbchs_SampleRate;
float thetalo = 2.0f * M_PI * (1200) / tbchs_SampleRate;
int16_t data[N];
int16_t coeffloi[N];
int16_t coeffloq[N];
int16_t coeffhii[N];
int16_t coeffhiq[N];
int16_t ptr=0;
#define PHASE_INC 65536 / N
#define  PHASE_CORR PHASE_INC / 2
uint16_t bit_phase;
int16_t last_inbyte=0;

//Moving averager
#define filtlength 5 //was 10
int avgcntj = 0;
int32_t filtoutput;
int32_t inputavg[filtlength]; 

//Synchronous Protocol
uint64_t  phasedetectbits=0; 
byte CodeState=1;
const byte DETECTED=2;
const byte HUNT=1;
byte cbyte =0;
byte rxByte[256];
int16_t bitcnt=8;
int16_t bytestoCount=256;
int16_t byteCnt=0;

//interleaver
#define numbits 2048
#define numbytes 256

byte symbols_interleaved[numbits];
byte b[numbits];
double flo;
double fhi;

//AO40FEC

#define Verbose 1      /* Permit some diagnostics; use 0 for none */

/* Defines for RS Decoder(s) */
#define min1(a,b)        ((a) < (b) ? (a) : (b))
#define NN        255
#define KK        223
#define NROOTS     32            /* NN-KK */
#define FCR       112
#define PRIM       11
#define IPRIM     116
#define AO        (NN)
#define BLOCKSIZE 256            /* Data bytes per frame */
#define RSBLOCKS    2            /* Number of RS decoder blocks */
#define RSPAD      95            /* Unused bytes in block  (KK-BLOCKSIZE/RSBLOCKS) */


/* Defines for Viterbi Decoder for r=1/2 k=7  (to CCSDS convention) */
#define K 7                      /* Constraint length */
#define NFEC 2                      /* Number of symbols per data bit */
#define CPOLYA 0x4f              /* First  convolutional encoder polynomial */
#define CPOLYB 0x6d              /* Second convolutional encoder polynomial */
#define PNPOLY     0x48 
/* Number of symbols in an FEC block that are */
/* passed to the Viterbi decoder  (320*8 + 6) */
#define NBITS ((BLOCKSIZE+NROOTS*RSBLOCKS)*8+K-1)

/* Defines for Interleaver */
#define ROWS       80            /* Block interleaver rows */
#define COLUMNS    65            /* Block interleaver columns */
#define SYMPBLOCK (ROWS*COLUMNS) /* Encoded symbols per block */

/* Defines for Re-encoder */
#define SYNC_POLY   0x48         /* Sync vector PN polynomial */
byte RSindata[256];
int Sync_vector[COLUMNS];
/* Tables moved out to a header file for clarity */
//#include "tables.h"
/*   Amsat P3 FEC Encoder/decoder system.   Look-up tables
 created by Phil Karn KA9Q and James Miller G3RUH
 Last modified 2003 Jun 20  */
int rp=0;
unsigned char raw[SYMPBLOCK] ;           /* 5200 raw received;  sync+symbols  */
unsigned char symbols[NBITS*2+65+3] ;    /* de-interleaved sync+symbols */
unsigned char vitdecdata[(NBITS-6)/8] ;  /* array for Viterbi decoder output data */
unsigned char RSdecdata[BLOCKSIZE] ;     /* RS decoder data output (to user)*/

long corr_amp;
long long energy;
//byte decoderbyte;
boolean bitshift=true;
/* Step 1: De-interleaver */

/* Input  array:  raw   */
/* Output array:  symbols */
int col,row;
int coltop,rowstart;

byte Interleaver[650];
/* 8-bit parity table */
unsigned char Partab[] = {
  0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
  1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
  1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
  0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
  1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
  0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
  0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
  1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
  1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
  0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
  0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
  1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
  0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
  1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
  1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
  0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
};

/* Tables for Viterbi r=1/2 k=7 decoder to CCSDS standard */
/* ------------------------------------------------------ */

/* Metric table, [sent sym][rx symbol] */
/* This metric table is for an 8-bit ADC, which is total overkill!
 Simplify later.  128-i and i-128 would probably do!  jrm */


int mettab[2][256]={
  {
    20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,
    20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,
    20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,
    20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,
    20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,
    20,   20,   20,   20,   20,   20,   20,   19,   19,   19,   19,   19,   19,   19,   19,   19,
    19,   19,   18,   18,   18,   18,   18,   18,   17,   17,   17,   16,   16,   16,   15,   15,
    14,   14,   13,   13,   12,   11,   10,   10,    9,    8,    7,    6,    5,    3,    2,    1,
    -1,   -2,   -4,   -5,   -7,   -9,  -11,  -13,  -15,  -17,  -19,  -21,  -23,  -25,  -28,  -30,
    -32,  -35,  -37,  -40,  -42,  -45,  -47,  -50,  -52,  -55,  -58,  -60,  -63,  -66,  -68,  -71,
    -74,  -77,  -79,  -82,  -85,  -88,  -90,  -93,  -96,  -99, -102, -104, -107, -110, -113, -116,
    -119, -121, -124, -127, -130, -133, -136, -138, -141, -144, -147, -150, -153, -155, -158, -161,
    -164, -167, -170, -172, -175, -178, -181, -184, -187, -190, -192, -195, -198, -201, -204, -207,
    -210, -212, -215, -218, -221, -224, -227, -229, -232, -235, -238, -241, -244, -247, -249, -252,
    -255, -258, -261, -264, -267, -269, -272, -275, -278, -281, -284, -286, -289, -292, -295, -298,
    -301, -304, -306, -309, -312, -315, -318, -320, -324, -326, -329, -332, -335, -337, -341, -372,
  }
  ,{
    -372, -341, -338, -335, -332, -329, -326, -324, -321, -318, -315, -312, -309, -306, -304, -301,
    -298, -295, -292, -289, -286, -284, -281, -278, -275, -272, -269, -267, -264, -261, -258, -255,
    -252, -249, -247, -244, -241, -238, -235, -232, -229, -227, -224, -221, -218, -215, -212, -210,
    -207, -204, -201, -198, -195, -192, -190, -187, -184, -181, -178, -175, -172, -170, -167, -164,
    -161, -158, -155, -153, -150, -147, -144, -141, -138, -136, -133, -130, -127, -124, -121, -119,
    -116, -113, -110, -107, -104, -102,  -99,  -96,  -93,  -90,  -88,  -85,  -82,  -79,  -77,  -74,
    -71,  -68,  -66,  -63,  -60,  -58,  -55,  -52,  -50,  -47,  -45,  -42,  -40,  -37,  -35,  -32,
    -30,  -28,  -25,  -23,  -21,  -19,  -17,  -15,  -13,  -11,   -9,   -7,   -5,   -4,   -2,   -1,
    1,    2,    3,    5,    6,    7,    8,    9,   10,   10,   11,   12,   13,   13,   14,   14,
    15,   15,   16,   16,   16,   17,   17,   17,   18,   18,   18,   18,   18,   18,   19,   19,
    19,   19,   19,   19,   19,   19,   19,   19,   19,   20,   20,   20,   20,   20,   20,   20,
    20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,
    20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,
    20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,
    20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,
    20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,   20,
  }
};


/* Table of symbol pair emitted for each state of the convolutional
 encoder's shift register */
int Syms[]={
  1, 2, 3, 0, 2, 1, 0, 3, 2, 1, 0, 3, 1, 2, 3, 0,
  1, 2, 3, 0, 2, 1, 0, 3, 2, 1, 0, 3, 1, 2, 3, 0,
  0, 3, 2, 1, 3, 0, 1, 2, 3, 0, 1, 2, 0, 3, 2, 1,
  0, 3, 2, 1, 3, 0, 1, 2, 3, 0, 1, 2, 0, 3, 2, 1,
  2, 1, 0, 3, 1, 2, 3, 0, 1, 2, 3, 0, 2, 1, 0, 3,
  2, 1, 0, 3, 1, 2, 3, 0, 1, 2, 3, 0, 2, 1, 0, 3,
  3, 0, 1, 2, 0, 3, 2, 1, 0, 3, 2, 1, 3, 0, 1, 2,
  3, 0, 1, 2, 0, 3, 2, 1, 0, 3, 2, 1, 3, 0, 1, 2, 
};

/* Tables for RS decoder */
/* Galois field log/antilog tables */
unsigned char ALPHA_TO1[] =
{
  0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x87, 0x89, 0x95, 0xad, 0xdd, 0x3d, 0x7a, 0xf4,
  0x6f, 0xde, 0x3b, 0x76, 0xec, 0x5f, 0xbe, 0xfb, 0x71, 0xe2, 0x43, 0x86, 0x8b, 0x91, 0xa5, 0xcd,
  0x1d, 0x3a, 0x74, 0xe8, 0x57, 0xae, 0xdb, 0x31, 0x62, 0xc4, 0x0f, 0x1e, 0x3c, 0x78, 0xf0, 0x67,
  0xce, 0x1b, 0x36, 0x6c, 0xd8, 0x37, 0x6e, 0xdc, 0x3f, 0x7e, 0xfc, 0x7f, 0xfe, 0x7b, 0xf6, 0x6b,
  0xd6, 0x2b, 0x56, 0xac, 0xdf, 0x39, 0x72, 0xe4, 0x4f, 0x9e, 0xbb, 0xf1, 0x65, 0xca, 0x13, 0x26,
  0x4c, 0x98, 0xb7, 0xe9, 0x55, 0xaa, 0xd3, 0x21, 0x42, 0x84, 0x8f, 0x99, 0xb5, 0xed, 0x5d, 0xba,
  0xf3, 0x61, 0xc2, 0x03, 0x06, 0x0c, 0x18, 0x30, 0x60, 0xc0, 0x07, 0x0e, 0x1c, 0x38, 0x70, 0xe0,
  0x47, 0x8e, 0x9b, 0xb1, 0xe5, 0x4d, 0x9a, 0xb3, 0xe1, 0x45, 0x8a, 0x93, 0xa1, 0xc5, 0x0d, 0x1a,
  0x34, 0x68, 0xd0, 0x27, 0x4e, 0x9c, 0xbf, 0xf9, 0x75, 0xea, 0x53, 0xa6, 0xcb, 0x11, 0x22, 0x44,
  0x88, 0x97, 0xa9, 0xd5, 0x2d, 0x5a, 0xb4, 0xef, 0x59, 0xb2, 0xe3, 0x41, 0x82, 0x83, 0x81, 0x85,
  0x8d, 0x9d, 0xbd, 0xfd, 0x7d, 0xfa, 0x73, 0xe6, 0x4b, 0x96, 0xab, 0xd1, 0x25, 0x4a, 0x94, 0xaf,
  0xd9, 0x35, 0x6a, 0xd4, 0x2f, 0x5e, 0xbc, 0xff, 0x79, 0xf2, 0x63, 0xc6, 0x0b, 0x16, 0x2c, 0x58,
  0xb0, 0xe7, 0x49, 0x92, 0xa3, 0xc1, 0x05, 0x0a, 0x14, 0x28, 0x50, 0xa0, 0xc7, 0x09, 0x12, 0x24,
  0x48, 0x90, 0xa7, 0xc9, 0x15, 0x2a, 0x54, 0xa8, 0xd7, 0x29, 0x52, 0xa4, 0xcf, 0x19, 0x32, 0x64,
  0xc8, 0x17, 0x2e, 0x5c, 0xb8, 0xf7, 0x69, 0xd2, 0x23, 0x46, 0x8c, 0x9f, 0xb9, 0xf5, 0x6d, 0xda,
  0x33, 0x66, 0xcc, 0x1f, 0x3e, 0x7c, 0xf8, 0x77, 0xee, 0x5b, 0xb6, 0xeb, 0x51, 0xa2, 0xc3, 0x00,
} 
;

unsigned char INDEX_OF1[]=
{
  0xff, 0x00, 0x01, 0x63, 0x02, 0xc6, 0x64, 0x6a, 0x03, 0xcd, 0xc7, 0xbc, 0x65, 0x7e, 0x6b, 0x2a,
  0x04, 0x8d, 0xce, 0x4e, 0xc8, 0xd4, 0xbd, 0xe1, 0x66, 0xdd, 0x7f, 0x31, 0x6c, 0x20, 0x2b, 0xf3,
  0x05, 0x57, 0x8e, 0xe8, 0xcf, 0xac, 0x4f, 0x83, 0xc9, 0xd9, 0xd5, 0x41, 0xbe, 0x94, 0xe2, 0xb4,
  0x67, 0x27, 0xde, 0xf0, 0x80, 0xb1, 0x32, 0x35, 0x6d, 0x45, 0x21, 0x12, 0x2c, 0x0d, 0xf4, 0x38,
  0x06, 0x9b, 0x58, 0x1a, 0x8f, 0x79, 0xe9, 0x70, 0xd0, 0xc2, 0xad, 0xa8, 0x50, 0x75, 0x84, 0x48,
  0xca, 0xfc, 0xda, 0x8a, 0xd6, 0x54, 0x42, 0x24, 0xbf, 0x98, 0x95, 0xf9, 0xe3, 0x5e, 0xb5, 0x15,
  0x68, 0x61, 0x28, 0xba, 0xdf, 0x4c, 0xf1, 0x2f, 0x81, 0xe6, 0xb2, 0x3f, 0x33, 0xee, 0x36, 0x10,
  0x6e, 0x18, 0x46, 0xa6, 0x22, 0x88, 0x13, 0xf7, 0x2d, 0xb8, 0x0e, 0x3d, 0xf5, 0xa4, 0x39, 0x3b,
  0x07, 0x9e, 0x9c, 0x9d, 0x59, 0x9f, 0x1b, 0x08, 0x90, 0x09, 0x7a, 0x1c, 0xea, 0xa0, 0x71, 0x5a,
  0xd1, 0x1d, 0xc3, 0x7b, 0xae, 0x0a, 0xa9, 0x91, 0x51, 0x5b, 0x76, 0x72, 0x85, 0xa1, 0x49, 0xeb,
  0xcb, 0x7c, 0xfd, 0xc4, 0xdb, 0x1e, 0x8b, 0xd2, 0xd7, 0x92, 0x55, 0xaa, 0x43, 0x0b, 0x25, 0xaf,
  0xc0, 0x73, 0x99, 0x77, 0x96, 0x5c, 0xfa, 0x52, 0xe4, 0xec, 0x5f, 0x4a, 0xb6, 0xa2, 0x16, 0x86,
  0x69, 0xc5, 0x62, 0xfe, 0x29, 0x7d, 0xbb, 0xcc, 0xe0, 0xd3, 0x4d, 0x8c, 0xf2, 0x1f, 0x30, 0xdc,
  0x82, 0xab, 0xe7, 0x56, 0xb3, 0x93, 0x40, 0xd8, 0x34, 0xb0, 0xef, 0x26, 0x37, 0x0c, 0x11, 0x44,
  0x6f, 0x78, 0x19, 0x9a, 0x47, 0x74, 0xa7, 0xc1, 0x23, 0x53, 0x89, 0xfb, 0x14, 0x5d, 0xf8, 0x97,
  0x2e, 0x4b, 0xb9, 0x60, 0x0f, 0xed, 0x3e, 0xe5, 0xf6, 0x87, 0xa5, 0x17, 0x3a, 0xa3, 0x3c, 0xb7,

} 
;

unsigned char Scrambler[]=
{
  0xff, 0x48, 0x0e, 0xc0, 0x9a, 0x0d, 0x70, 0xbc, 0x8e, 0x2c, 0x93, 0xad, 0xa7, 0xb7, 0x46, 0xce,
  0x5a, 0x97, 0x7d, 0xcc, 0x32, 0xa2, 0xbf, 0x3e, 0x0a, 0x10, 0xf1, 0x88, 0x94, 0xcd, 0xea, 0xb1,
  0xfe, 0x90, 0x1d, 0x81, 0x34, 0x1a, 0xe1, 0x79, 0x1c, 0x59, 0x27, 0x5b, 0x4f, 0x6e, 0x8d, 0x9c,
  0xb5, 0x2e, 0xfb, 0x98, 0x65, 0x45, 0x7e, 0x7c, 0x14, 0x21, 0xe3, 0x11, 0x29, 0x9b, 0xd5, 0x63,
  0xfd, 0x20, 0x3b, 0x02, 0x68, 0x35, 0xc2, 0xf2, 0x38, 0xb2, 0x4e, 0xb6, 0x9e, 0xdd, 0x1b, 0x39,
  0x6a, 0x5d, 0xf7, 0x30, 0xca, 0x8a, 0xfc, 0xf8, 0x28, 0x43, 0xc6, 0x22, 0x53, 0x37, 0xaa, 0xc7,
  0xfa, 0x40, 0x76, 0x04, 0xd0, 0x6b, 0x85, 0xe4, 0x71, 0x64, 0x9d, 0x6d, 0x3d, 0xba, 0x36, 0x72,
  0xd4, 0xbb, 0xee, 0x61, 0x95, 0x15, 0xf9, 0xf0, 0x50, 0x87, 0x8c, 0x44, 0xa6, 0x6f, 0x55, 0x8f,
  0xf4, 0x80, 0xec, 0x09, 0xa0, 0xd7, 0x0b, 0xc8, 0xe2, 0xc9, 0x3a, 0xda, 0x7b, 0x74, 0x6c, 0xe5,
  0xa9, 0x77, 0xdc, 0xc3, 0x2a, 0x2b, 0xf3, 0xe0, 0xa1, 0x0f, 0x18, 0x89, 0x4c, 0xde, 0xab, 0x1f,
  0xe9, 0x01, 0xd8, 0x13, 0x41, 0xae, 0x17, 0x91, 0xc5, 0x92, 0x75, 0xb4, 0xf6, 0xe8, 0xd9, 0xcb,
  0x52, 0xef, 0xb9, 0x86, 0x54, 0x57, 0xe7, 0xc1, 0x42, 0x1e, 0x31, 0x12, 0x99, 0xbd, 0x56, 0x3f,
  0xd2, 0x03, 0xb0, 0x26, 0x83, 0x5c, 0x2f, 0x23, 0x8b, 0x24, 0xeb, 0x69, 0xed, 0xd1, 0xb3, 0x96,
  0xa5, 0xdf, 0x73, 0x0c, 0xa8, 0xaf, 0xcf, 0x82, 0x84, 0x3c, 0x62, 0x25, 0x33, 0x7a, 0xac, 0x7f,
  0xa4, 0x07, 0x60, 0x4d, 0x06, 0xb8, 0x5e, 0x47, 0x16, 0x49, 0xd6, 0xd3, 0xdb, 0xa3, 0x67, 0x2d,
  0x4b, 0xbe, 0xe6, 0x19, 0x51, 0x5f, 0x9f, 0x05, 0x08, 0x78, 0xc4, 0x4a, 0x66, 0xf5, 0x58, 0xff,
  0x48, 0x0e, 0xc0, 0x9a, 0x0d, 0x70, 0xbc, 0x8e, 0x2c, 0x93, 0xad, 0xa7, 0xb7, 0x46, 0xce, 0x5a,
  0x97, 0x7d, 0xcc, 0x32, 0xa2, 0xbf, 0x3e, 0x0a, 0x10, 0xf1, 0x88, 0x94, 0xcd, 0xea, 0xb1, 0xfe,
  0x90, 0x1d, 0x81, 0x34, 0x1a, 0xe1, 0x79, 0x1c, 0x59, 0x27, 0x5b, 0x4f, 0x6e, 0x8d, 0x9c, 0xb5,
  0x2e, 0xfb, 0x98, 0x65, 0x45, 0x7e, 0x7c, 0x14, 0x21, 0xe3, 0x11, 0x29, 0x9b, 0xd5, 0x63, 0xfd,
} 
;

int cntfec=0;
int fecmetriccnt;
int fecmetric;



//ENDAO40FEC


void  tbchs::tx_init(SoundBase *sc)
{
	scard = sc;
}

void  tbchs::rx_init()
{
	if (fl_digi_main)
		put_MODEstatus(mode);
	set_freq(1700);
	set_scope_mode(Digiscope::RTTY);
	initmatchedfilter();
	inp_ptr = 0;
}

void tbchs::init()
{
	modem::init();
	rx_init();
	//if (digiscope)
	//	digiscope->mode(Digiscope::RTTY);
	init_sync();
	put_rx_char('T');
	put_rx_char('e');
	put_rx_char('s');
	put_rx_char('t');
}

tbchs::~tbchs()
{
	 delete bandpass;
	/*delete hilbert;
	delete lowpass;
	delete sliding;
	delete [] scope_data;
	delete [] out_buf;
	delete [] in_buf;*/
	if (pipe) delete [] pipe;
	if (dsppipe) delete [] dsppipe;
}

tbchs::tbchs() : modem()
{
	//double cf, flo, fhi;

	mode =MODE_tbchs;
	samplerate = tbchs_SampleRate;
	restart();
	pipe = new double[MAXPIPE];
	dsppipe = new double [MAXPIPE];
	pipeptr = 0;
    flo = 1100.0 / 48000.0;	
    fhi = 2300.0 / 48000.0;	
	bandpass	= new C_FIR_filter();
	bandpass->init_bandpass (151, 1, flo, fhi );
	//lowpass= new C_FIR_filter();
	//lowpass->init_lowpass (127, 1, fhi);
	/*symlen = SYMLEN;
	bandwidth = tbchs_BW;
	samplerate = tbchsSampleRate;
	
	flo = LP_F1 / corrRxSampleRate();	
	lowpass		= new C_FIR_filter();
	lowpass->init_lowpass (LP_FIRLEN, LP_DEC, flo );
	
	flo = BP_F1 / corrRxSampleRate();	
	fhi = BP_F2 / corrRxSampleRate();	
	bandpass	= new C_FIR_filter();
	bandpass->init_bandpass (BP_FIRLEN, BP_DEC, flo, fhi );

	hilbert		= new C_FIR_filter();
	hilbert->init_hilbert(37, 1);

	sliding		= new sfft (SL_LEN, SL_F1, SL_F2); // all integer values

	scope_data	= new double [SCOPE_DATA_LEN];
	out_buf		= new double [SYMLEN];
	in_buf		= new double [BUFLEN];
	*/
//	init();
}

//=====================================================================
// receive processing
//=====================================================================

/*void tbchs::recvchar(int c)
{
	if (c == -1)
		return;
	put_rx_char(c);
}

*/
cmplx tbchs::mixer(cmplx in, double f)
{
	cmplx z (cos(phaseacc), sin(phaseacc));
	z = z * in;

	phaseacc += TWOPI * frequency / samplerate;
	if (phaseacc > M_PI)
		phaseacc -= TWOPI;
	else if (phaseacc < M_PI)
		phaseacc += TWOPI;

	return z;
}

void tbchs::update_syncscope()
{

	int j;
	for (int i = 0; i < N; i++) {
		j = pipeptr - i;
		if (j < 0) j += N;
		dsppipe[i] = pipe[j];
	}
	set_scope(dsppipe, N, false);
}



/*void tbchs::afc()
{
	complex z;
	double x;

	if (metric < squelch)
		return;
// adjust "frequency" iaw with afc processing
}*/

int tbchs::rx_process(const double *buf, int len)
{
	
	cmplx z;
	cmplx a;
	int tlen=len;
	double bufp[len];
	int index=0;
	
	while (tlen-- > 0) {
	z = cmplx( *buf,0 );
	// snprintf(msg, sizeof(msg), "RSCorr %f", z.real());
   //  put_Status2(msg);
	buf++;
	//hbfilt->run ( z, z );
	bandpass->run (z,a);	
	//bufp[index]= sqrt(a.real()*a.real()+a.imag()*a.imag());
	bufp[index]= a.real();
	//snprintf(msg, sizeof(msg), "RSCorr %f", a.real());
    //put_Status2(msg);
	index++;
	}
	
	
	/*char msg[80];
	const double *tdbl;
	double *outdbl;
	int index=0;
	double bufp[len];
	int tlen=len;
	while (tlen-- > 0) {
	
	bandpass->Irun ( buf[index],*outdbl);
	bufp[index]=*outdbl;
	//*buf++;
	 snprintf(msg, sizeof(msg), "RSCorr %f", *outdbl);
     put_Status2(msg);
	index++;
	}*/
	
	/*
	complex z;
	int i;

	while (len-- > 0) {
// create analytic signal...
		z.re = z.im = *buf++;
		hbfilt->run ( z, z );
// shift in frequency to the base freq of 1000 hz
		z = mixer(z, frequency);
// bandpass filter around the shifted center frequency
// with required bandwidth 
		bandpass->run ( z, z );
		
// binsfft->run(z) copies frequencies of interest
		complex dummy ;
		sliding->run (z, &dummy, 0 );
// etc
		decodesymbol();
		update_syncscope();
		afc();
	}*/
	
	//digiscope->video((double*)buf,len,false);
	
	int16_t tint;
	
	for(int i=0;i < len;i++){
        tint=bufp[i]*2047;//was *2047
		//fint=runFiltAverager(tint);
		if(demodulate(tint)> 0) decode(1); else decode(0); //was 10
	}
	// digiscope->draw_rtty();
	return 0;
}
void tbchs::initmatchedfilter(){

  for (int i = 0; i < N ; i++)
 /* {
	   coeffloi[i] = (short)((Math.Cos(i * thetalo)) * 32767);
       coeffloq[i] = (short)((Math.Sin(i * thetalo)) * 32767);
       coeffhii[i] = (short)((Math.Cos(i * thetahi)) * 32767);
       coeffhiq[i] = (short)((Math.Sin(i * thetahi)) * 32767);
  }          */
  {
    coeffloi[i] = (cos(i*thetalo)* 32767);
    coeffloq[i] = (sin(i*thetalo)* 32767);
    coeffhii[i] = (cos(i*thetahi)* 32767);
    coeffhiq[i] = (sin(i*thetahi) * 32767);
  
  }
}

int32_t tbchs::demodulate(int16_t input) {

  int16_t d;
  int32_t outloi=0,outloq=0,outhii=0,outhiq=0,output;
  data[ptr]=input; 
  ptr = ((ptr+1)%N); /* % : Modulo */
  for(int i=0;i<N;i++) {
    d = data[(ptr+i)%N];
    outloi += d*coeffloi[i];
    outloq += d*coeffloq[i];
    outhii += d*coeffhii[i];
    outhiq += d*coeffhiq[i];
  }

   // output =(((outhii / 5120000 * outhii / 5120000) + (outhiq / 5120000 * outhiq / 5120000)) - ((outloi / 5120000) * (outloi / 5120000) + (outloq / 5120000) * (outloq / 5120000)));
   output =(outhii >>15) * (outhii >>15) + (outhiq >>15) * (outhiq>>15) - (outloi >>15) * (outloi >>15) - (outloq >> 15) * (outloq >>15);
   output = runFiltAverager(output);
  // if (Math.Abs(output) < 100) output = 0;
  return output;
}


int  tbchs::decodeGold1( uint64_t keycode)
{
  /***************************************************************************/
  // Autocorrelation calculation for a 64-bit correlation tag value
  //
  // Data is stored locally in a static 64-bit variable.  The most recent byte
  // provides the next 8 bits in time sequence, and is shifted-in to the LSB
  // position of the holding register.  The MSB of the holding register is the 
  // oldest in time-sequence.  
  //
  // The calculated autocorrelation values are compared to the threshold parameter.  If the 
  // threshold isn't met, a phase value of 8 is returned - indicating that the tag wasn't found.
  // Valid bit-phase values of 7:0 indicate that the tag was found.
  //
  // So what does this all mean?  If the autocorrelation value exceeds your threshold, that
  // indicates a "match."  The correlation tag begins in the data[0] byte at the bit-offset,
  // and terminates at the bit-offset in the MSB of ltemp1.  For the degenerate case where 
  // the bit-offset is zero, "data" represents the last byte of the correlationt tag, and
  // the next byte in time sequence will be an information byte.
  //
  //
  /***************************************************************************/

  

  // iterate through 8 bit-phase shifts (that's zero plus 7 offsets)

  ltemp2 = keycode;

  int    sum = 0;
  for (int i = 0; i < 64; i++)
  {
    if (((ltemp2 >> i) & 0x01) == ((tag >> i) & 0x01))
      sum++;
    else
      sum--;
  }
  return (sum);
}

void tbchs::decode(int16_t inbyte) {
  int32_t temp;
  if (last_inbyte != inbyte)
  {
    if (bit_phase < 0x8000){
      bit_phase += PHASE_CORR;
    }
    else{

      bit_phase -= PHASE_CORR;
    }
  }

  temp = bit_phase + PHASE_INC;
  bit_phase =(uint16_t)(temp & 0xffff);
  if (temp > 0xffff)
  {
   // bitinwithGC(inbyte);
	 decodeAO40bit((unsigned char)inbyte);
	//bitinwithGCFEC(inbyte);
	inp_ptr = (inp_ptr + 1) % MAXPIPE;

  if (dspcnt1 && (--dspcnt1 % (8) == 0)) {
	pipe[pipeptr] = inbyte - 0.5; //testbit - 0.5;
	pipeptr = (pipeptr + 1) % N;
   }
  
  
    //Send inbyte for decoding   
    
  }  
  last_inbyte = inbyte;//This was is for the clocking

  

}          

//Synchronous protocol routines
int tbchs::getData10(byte bitin)
{       
  if (bitin == 1) bitin = 0x80;
  cbyte = (byte)(cbyte >> 1);
  cbyte = (byte)((int)cbyte | (int)bitin);

  bitcnt--;
  if (bitcnt == 0)
  {          
    bitcnt = 8;
    // cbyte = 0;
    return 2;
  }
  return 3;
}
//Detect Gold Code

int tbchs::getData1(byte bitin)
{

  if (CodeState == DETECTED)
  {
    return (getData10(bitin));
  }

  uint64_t bitin64=0;

  if (bitin == 1) bitin64 = 0x8000000000000000;
  phasedetectbits = (phasedetectbits >> 1);
  phasedetectbits = ((uint64_t)phasedetectbits | (uint64_t)bitin64);

  int sum = decodeGold1(phasedetectbits); 
  display_metric(sum*2);
  if (sum > 40){
    bitcnt = 8;
	put_rx_char('G');
    //Serial.print("Correlation found");
    return 2;
  }

  return 3;
}



     

int32_t tbchs::runFiltAverager(int32_t datain){	    
  filtoutput = filtoutput - inputavg[avgcntj] + datain;
  inputavg[avgcntj] = datain;
  if (++avgcntj >= filtlength) avgcntj = 0;
  return (filtoutput / filtlength);
}

void tbchs::bitinwithGC(int bitin)
{
  

  if(getData1((byte)bitin) == 2){//0501vk3tbc
	  update_syncscope();
	  dspcnt1 = N * (8);
	  uint16_t intcrc;

    switch (CodeState)
    {
    default:
    case HUNT:   
      bytestoCount = 256;
      CodeState = DETECTED;
      cbyte = 0;
      byteCnt = 0;    
      break;

    case DETECTED:

      rxByte[byteCnt++] = cbyte;

      if (byteCnt == bytestoCount)
      {
       
        deshuffle(rxByte);
       
			
		
        //uint8_t pkt[256];
  
        int rscorr;

        /* Testing is destructive, work on a copy */
        memcpy(pkt,rxByte, 256);
        rscorr = decode_rs_8(&pkt[0], 0, 0, 0);
		//i = decode_rs_8(&pkt[1], eras_pos, no_eras, 0);
       // memcpy(rxByte, pkt, 256);
		 for(int i=0;i<256;i++){
			  put_rx_ssdv(rxByte[i], 0);
		  }
        /*Check if it is telemetry or image*/
       /* if ((rscorr >= 0)&&(pkt[0]!=0x24))
        {
          for(int i=0;i<256;i++){
			  put_rx_ssdv(rxByte[i], 0);
		  }
        
		}else */ if ((rscorr >= 0)&&(pkt[0]==0x24)) {
			string strtoparse="                                                         ";
            for(int i = 0;i<57;i++){
             strtoparse[i]=((char)(pkt[i]));
			
           }
          char msg[80];
		  snprintf(msg, sizeof(msg), "RSCorr %d", rscorr);
		  put_Status2(msg);
		    /*
          TNCAX25Emulator.Receivedparameters.psbcallsign = FastTelemetry.Substring(2, 6);
           TNCAX25Emulator.Receivedparameters.sequence = FastTelemetry.Substring(8, 4);
           TNCAX25Emulator.Receivedparameters.time = FastTelemetry.Substring(12, 8);
           TNCAX25Emulator.Receivedparameters.lat = FastTelemetry.Substring(20, 8);
           TNCAX25Emulator.Receivedparameters.longitude = FastTelemetry.Substring(28, 9);
           TNCAX25Emulator.Receivedparameters.altiude = FastTelemetry.Substring(37, 5);
           TNCAX25Emulator.Receivedparameters.speed = FastTelemetry.Substring(42, 3);
           TNCAX25Emulator.Receivedparameters.satno = FastTelemetry.Substring(45, 2);
           TNCAX25Emulator.Receivedparameters.gpsfix = FastTelemetry.Substring(47, 1);
           TNCAX25Emulator.Receivedparameters.tin = FastTelemetry.Substring(48, 3);
           TNCAX25Emulator.Receivedparameters.tout = FastTelemetry.Substring(51, 3);
           TNCAX25Emulator.Receivedparameters.volts = FastTelemetry.Substring(54, 3);
           */
           strtoparse[57] = '\0';
		   memset (payloadtxt, 0, 90); 
		   memset (payloadtxtfinal, 0, 90); 
		   try
           { 
		   comma = ",";
		    asterisk ="*";
		    dollar= "$$";
			lcallsign =  strtoparse.substr(2,6);
			sequence = strtoparse.substr(8,4);
		    ltime = strtoparse.substr(12,8);
		    latstring = strtoparse.substr(20,8);
			longstring = strtoparse.substr(28,9);
			altitude = strtoparse.substr(37,5);
			speed = strtoparse.substr(42,3);
			satno  = strtoparse.substr(45,2);
		    satfix  = strtoparse.substr(47,1);
			insidetemp = strtoparse.substr(48,3);
		    outsidetemp = strtoparse.substr(51,3);
			volts = strtoparse.substr(54,3);   
		    strcat(payloadtxtfinal,dollar.c_str());
		    strcat(payloadtxt,lcallsign.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,sequence.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,ltime.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,latstring.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,longstring.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,altitude.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,speed.c_str());
		    strcat(payloadtxt,comma.c_str());
			strcat(payloadtxt,satno.c_str());
		    strcat(payloadtxt,comma.c_str());
			strcat(payloadtxt,satfix.c_str());
		    strcat(payloadtxt,comma.c_str());
			strcat(payloadtxt,insidetemp.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,outsidetemp.c_str());
		    strcat(payloadtxt,comma.c_str());
			strcat(payloadtxt,volts.c_str());
			s=string(payloadtxt);
		    intcrc = crtty_CRC16_checksum (payloadtxt,66) ;
			char temp[5];
            snprintf(temp, sizeof(temp), "%.04X", intcrc);
			//checksum_crc16_ccitt();			
		    strcat(payloadtxt,asterisk.c_str());
			//strcat(payloadtxt,crcstr.c_str());
			strcat(payloadtxt,temp);
			for(int i=0;i<80;i++){
				payloadtxtfinal[i+2]=payloadtxt[i];
				
			}
			//strcat(payloadtxtfinal,(((string)payloadtxt).c_str()));
		   }
		   catch (int e)
           {
            put_rx_char('E');
			put_rx_char('R');
           }
			char *testp  = "PSB,0001,000000,0.0,0.0,0,0,0,0,107,26,7656";
			
			
             char hex[4];
             sprintf(hex, "%04x", intcrc);
			//  put_rx_char('\n');
			 for(int i=0;i<4;i++){
				 hex[i]=toupper(hex[i]);
				// put_rx_char(hex[i]);
			 }
			//  put_rx_char('\n');
			// strcat(payloadtxt,hex);
			//string testpsb= "PSB,0001,000000,0.0,0.0,0,0,0,0,107,26,7656";
			
			
			 for(int i=0;i<73;i++){
			     put_rx_char(payloadtxtfinal[i]);
			 }
			 put_rx_char('\n');
		}
		 
        memset (rxByte, 0, 256); 
		memset(pkt,0,256);
        byteCnt = 0;
        CodeState = HUNT;
        
    

      break;
    }
  }
 }
}
void tbchs::storeandisplayFECdata(byte* rxByte){
	uint16_t intcrc;
	//memcpy(pkt,rxByte, 256);
    //int rscorr = decode_rs_8(&pkt[0], 0, 0, 0);
	//update_syncscope();
    //dspcnt1 = N * (8);
	for(int i=0;i<256;i++){
			  put_rx_ssdv(rxByte[i], 0);
			  update_syncscope();
              dspcnt1 = N * (8);
		  }
	if (rxByte[0]==0x24) {
			string strtoparse="                                                         ";
            for(int i = 0;i<57;i++){
             strtoparse[i]=((char)(rxByte[i]));
			
           }
    
	strtoparse[57] = '\0';
	memset (payloadtxt, 0, 90); 
	memset (payloadtxtfinal, 0, 90); 
	try
           { 
		   comma = ",";
		    asterisk ="*";
		    dollar= "$$";
			lcallsign =  strtoparse.substr(2,6);
			sequence = strtoparse.substr(8,4);
		    ltime = strtoparse.substr(12,8);
		    latstring = strtoparse.substr(20,8);
			longstring = strtoparse.substr(28,9);
			altitude = strtoparse.substr(37,5);
			speed = strtoparse.substr(42,3);
			satno  = strtoparse.substr(45,2);
		    satfix  = strtoparse.substr(47,1);
			insidetemp = strtoparse.substr(48,3);
		    outsidetemp = strtoparse.substr(51,3);
			volts = strtoparse.substr(54,3);   
		    strcat(payloadtxtfinal,dollar.c_str());
		    strcat(payloadtxt,lcallsign.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,sequence.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,ltime.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,latstring.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,longstring.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,altitude.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,speed.c_str());
		    strcat(payloadtxt,comma.c_str());
			strcat(payloadtxt,satno.c_str());
		    strcat(payloadtxt,comma.c_str());
			strcat(payloadtxt,satfix.c_str());
		    strcat(payloadtxt,comma.c_str());
			strcat(payloadtxt,insidetemp.c_str());
		    strcat(payloadtxt,comma.c_str());
		    strcat(payloadtxt,outsidetemp.c_str());
		    strcat(payloadtxt,comma.c_str());
			strcat(payloadtxt,volts.c_str());
			s=string(payloadtxt);
		    intcrc = crtty_CRC16_checksum (payloadtxt,66) ;
			char temp[5];
            snprintf(temp, sizeof(temp), "%.04X", intcrc);		
		    strcat(payloadtxt,asterisk.c_str());
			strcat(payloadtxt,temp);
			for(int i=0;i<80;i++){
				payloadtxtfinal[i+2]=payloadtxt[i];
				
			}
			
		   }
	catch (int e)
           {
            put_rx_char('E');
			put_rx_char('R');
           }
	for(int i=0;i<73;i++){
			put_rx_char(payloadtxtfinal[i]);
		   }
	put_rx_char('\n');

    }
}
void tbchs::checksum_crc16_ccitt()
{
    /* From avr-libc docs: Modified BSD (GPL, BSD, DFSG compatible) */
    uint16_t crc = 0xFFFF;

    for (string::const_iterator it = s.begin(); it != s.end(); it++)
    {
       
		crc = crc ^ ((uint16_t (*it)) << 8);

        for (int i = 0; i < 8; i++)
        {
            bool s = crc & 0x8000;
            crc <<= 1;
            crc ^= (s ? 0x1021 : 0);
        }
    }

    char temp[5];
    snprintf(temp, sizeof(temp), "%.04X", crc);
	crcstr = string(temp);
  //  return string(temp);
	
}

uint16_t tbchs::crtty_CRC16_checksum (char rxBytepacket[],int length) 
{
  //$$PSB,0001,000000,0.0,0.0,0,0,0,0,107,26,7656*16B3     //Test string   CRC on everything between $$ and * last 4 byte is rx crc
  uint16_t crc=0xFFFF;
  //String ln= "Length " + String(length);
  // Serial.print(ln);
  byte c;    
  // Calculate checksum ignoring the first two $s
  for (int i = 0; i < length; i++)//46
  {
   // put_rx_char(rxBytepacket[i]);
	c = (byte) rxBytepacket[i];
   
    uint16_t cr = (uint16_t)(c << 8);
    crc = (uint16_t)(crc ^ (cr));
    for (int x = 0; x < 8; x++)
    {
      if ((crc & 0x8000) == 0x8000)
        crc = (uint16_t)((crc << 1) ^ 0x1021);
      else
        crc = (uint16_t) (crc << 1);
    }               
  }

  return crc;
}
void tbchs::deshuffle(byte *rxbuf)

{
 
  byte bitin;
  byte cbyte = 0;

  for (int i = 0; i < 256; i++)
  {

    cbyte=rxbuf[i];
    for (int bi = 0; bi < 8; bi++)
    {
      symbols_interleaved[bi + (8 * i)]=cbyte&0x80;
      if(symbols_interleaved[bi + (8 * i)]==0x80) 
      {
        symbols_interleaved[bi + (8 * i)]=1;
      }
      cbyte=cbyte<<1;

    }   

  }

   deinterleaver1();
  for (int i = 0; i < numbytes; i++){

    for (int bi = 0; bi < 8; bi++)
    {

      bitin = b[bi + (8 * i)];
      cbyte = (byte)(cbyte << 1);
      cbyte = (byte)((int)cbyte | (int)bitin);

      //Console.WriteLine(cbyte);
    }
    //   Console.Write(cbyte+" ");
    rxbuf[i] = cbyte;
    cbyte = 0;
  }
  return;
}

void tbchs::deinterleaver1()//input symbols_interleaved
{

  int i, j, k, l, P;

  P = 0;
  while (P < numbits)
  {
    for (k = 0; k <= 2047; k++)                        // bits reverse, ex: 0010 1110 --> 0111 0100
    {
      i = k;
      j = 0;
      for (l = 10; l >= 0; l--)                      // hard work is done here...
      {
        j = j | (i & 0x01) << l;
        i = i >> 1;
      }
      if (j < numbits)
        b[P++] = symbols_interleaved[j];    // range in interleaved table
    }                                             // end of while, interleaved table is full
  }
  return ;
}









//=====================================================================
// transmit processing
//=====================================================================




void sendidle() {
}

int tbchs::tx_process()
{MilliSleep(10);
	if (!fl_digi_main) return 0;
	
	if ( get_tx_char() == GET_TX_CHAR_ETX || stopflag) {
		stopflag = false;
		return -1;
	}
	return 0;
}

void tbchs::restart(){
		if (wf) set_bandwidth(1000);
}

/* ----------------------------------------------------------------------------------- */

/* --------------- */
/* Viterbi decoder */
/* --------------- */

/* Viterbi decoder for arbitrary convolutional code
 * viterbi27 and viterbi37 for the r=1/2 and r=1/3 K=7 codes are faster
 * Copyright 1997 Phil Karn, KA9Q
 */

/* This is a bare bones <2,7> Viterbi decoder, adapted from a general purpose model.
 * It is not optimised in any way, neither as to coding (for example the memcopy should
 * be achievable simply by swapping pointers), nor as to simplifying the metric table,
 * nor as to using any machine-specific smarts.  On contemporary machines, in this application,
 * the execution time is negligible.  Many ideas for optimisation are contained in PK's www pages.
 * The real ADC is 8-bit, though in practice 4-bits are actually sufficient.
 * Descriptions of the Viterbi decoder algorithm can be found in virtually any book
 * entitled "Digital Communications".  (JRM)
 */

int tbchs::viterbi27(
unsigned char *data,          /* Decoded output data */
unsigned char *symbols,       /* Raw deinterleaved input symbols */
unsigned int nbits )          /* Number of output bits */

{
  unsigned int bitcnt = 0;
  int beststate,i,j;
  long cmetric[64],nmetric[64];    /* 2^(K-1) */
  unsigned long *pp;
  long m0,m1,mask;
  int mets[4];                     /* 2^N */
  unsigned long *paths;


  pp = paths = (unsigned long *)calloc(nbits*2,sizeof(unsigned long));
  /* Initialize starting metrics to prefer 0 state */
  cmetric[0] = 0;
  for(i=1;i< 64;i++)
    cmetric[i] = -999999;

  for(;;){
    /* Read 2 input symbols and compute the 4 branch metrics */
    for(i=0;i<4;i++){
      mets[i] = 0;
      for(j=0;j<2;j++){
        mets[i] += mettab[(i >> (1-j)) & 1][symbols[j]];
      }
    }
    symbols += 2;
    mask = 1;
    for(i=0;i<64;i+=2){
      int b1,b2;

      b1 = mets[Syms[i]];
      nmetric[i] = m0 = cmetric[i/2] + b1;
      b2 = mets[Syms[i+1]];
      b1 -= b2;
      m1 = cmetric[(i/2) + (1<<(K-2))] + b2;
      if(m1 > m0){
        nmetric[i] = m1;
        *pp |= mask;
      }
      m0 -= b1;
      nmetric[i+1] = m0;
      m1 += b1;
      if(m1 > m0){
        nmetric[i+1] = m1;
        *pp |= mask << 1;
      }
      mask <<= 2;
      if(mask == 0){
        mask = 1;
        pp++;
      }
    }
    if(mask != 1)
      pp++;
    if(++bitcnt == nbits){
      beststate = 0;

      break;
    }
    memcpy(cmetric,nmetric,sizeof(cmetric));
  }
  pp -= 2;
  /* Chain back from terminal state to produce decoded data */
  memset(data,0,nbits/8);
  for(i=nbits-K;i >= 0;i--){
    if(pp[beststate >> 5] & (1L << (beststate & 31))){
      beststate |= (1 << (K-1));
      data[i>>3] |= 0x80 >> (i&7);
    }
    beststate >>= 1;
    pp -= 2;
  }
  free(paths);
  return 0;
}

/* ----------------------------------------------------------------------------------- */

/* ---------- */
/* RS Decoder */
/* ---------- */

/* This decoder has evolved extensively through the work of Phil Karn.  It draws
 * on his own ideas and optimisations, and on the work of others.  The lineage
 * is as below, and parts of the authors' notices are included here.  (JRM)
 
 * Reed-Solomon decoder
 * Copyright 2002 Phil Karn, KA9Q
 * May be used under the terms of the GNU General Public License (GPL)
 *
 * Reed-Solomon coding and decoding
 * Phil Karn (karn@ka9q.ampr.org) September 1996
 *
 * This file is derived from the program "new_rs_erasures.c" by Robert
 * Morelos-Zaragoza (robert@spectra.eng.hawaii.edu) and Hari Thirumoorthy
 * (harit@spectra.eng.hawaii.edu), Aug 1995
 * --------------------------------------------------------------------------
 *
 * From the RM-Z & HT program:
 * The encoding and decoding methods are based on the
 * book "Error Control Coding: Fundamentals and Applications",
 * by Lin and Costello, Prentice Hall, 1983, ISBN 0-13-283796-X
 * Portions of this program are from a Reed-Solomon encoder/decoder
 * in C, written by Simon Rockliff (simon@augean.ua.oz.au) on 21/9/89.
 * --------------------------------------------------------------------------
 *
 * From the 1989/1991 SR program (also based on Lin and Costello):
 * This program may be freely modified and/or given to whoever wants it.
 * A condition of such distribution is that the author's contribution be
 * acknowledged by his name being left in the comments heading the program,
 *                               Simon Rockliff, 26th June 1991
 *
 */

int tbchs::mod255(int x){
  while (x >= 255) {
    x -= 255;
    x = (x >> 8) + (x & 255);
  }
  return x;
}



int tbchs::decode_rs_8_fec(char *data, int *eras_pos, int no_eras){

  int deg_lambda, el, deg_omega;
  int i, j, r,k;
  unsigned char u,q,tmp,num1,num2,den,discr_r;
  unsigned char lambda[NROOTS+1], s[NROOTS];   /* Err+Eras Locator poly and syndrome poly */
  unsigned char b[NROOTS+1], t[NROOTS+1], omega[NROOTS+1];
  unsigned char root[NROOTS], reg[NROOTS+1], loc[NROOTS];
  int syn_error, count;

  /* form the syndromes; i.e., evaluate data(x) at roots of g(x) */
  for(i=0;i<NROOTS;i++)
    s[i] = data[0];

  for(j=1;j<NN;j++){
    for(i=0;i<NROOTS;i++){
      if(s[i] == 0){
        s[i] = data[j];
      } 
      else {
        s[i] = data[j] ^ ALPHA_TO1[mod255(INDEX_OF1[s[i]] + (FCR+i)*PRIM)];
      }
    }
  }

  /* Convert syndromes to index form, checking for nonzero condition */
  syn_error = 0;
  for(i=0;i<NROOTS;i++){
    syn_error |= s[i];
    s[i] = INDEX_OF1[s[i]];
  }

  if (!syn_error) {
    /* if syndrome is zero, data[] is a codeword and there are no
     * errors to correct. So return data[] unmodified
     */
    count = 0;
    goto finish;
  }
  memset(&lambda[1],0,NROOTS*sizeof(lambda[0]));
  lambda[0] = 1;

  if (no_eras > 0) {
    /* Init lambda to be the erasure locator polynomial */
    lambda[1] = ALPHA_TO1[mod255(PRIM*(NN-1-eras_pos[0]))];
    for (i = 1; i < no_eras; i++) {
      u = mod255(PRIM*(NN-1-eras_pos[i]));
      for (j = i+1; j > 0; j--) {
        tmp = INDEX_OF1[lambda[j - 1]];
        if(tmp != AO)
          lambda[j] ^= ALPHA_TO1[mod255(u + tmp)];
      }
    }
  }
  for(i=0;i<NROOTS+1;i++)
    b[i] = INDEX_OF1[lambda[i]];

  /*
   * Begin Berlekamp-Massey algorithm to determine error+erasure
   * locator polynomial
   */
  r = no_eras;
  el = no_eras;
  while (++r <= NROOTS) {       /* r is the step number */
    /* Compute discrepancy at the r-th step in poly-form */
    discr_r = 0;
    for (i = 0; i < r; i++){
      if ((lambda[i] != 0) && (s[r-i-1] != AO)) {
        discr_r ^= ALPHA_TO1[mod255(INDEX_OF1[lambda[i]] + s[r-i-1])];
      }
    }
    discr_r = INDEX_OF1[discr_r];        /* Index form */
    if (discr_r == AO) {
      /* 2 lines below: B(x) <-- x*B(x) */
      memmove(&b[1],b,NROOTS*sizeof(b[0]));
      b[0] = AO;
    } 
    else {
      /* 7 lines below: T(x) <-- lambda(x) - discr_r*x*b(x) */
      t[0] = lambda[0];
      for (i = 0 ; i < NROOTS; i++) {
        if(b[i] != AO)
          t[i+1] = lambda[i+1] ^ ALPHA_TO1[mod255(discr_r + b[i])];
        else
          t[i+1] = lambda[i+1];
      }
      if (2 * el <= r + no_eras - 1) {
        el = r + no_eras - el;
        /*
         * 2 lines below: B(x) <-- inv(discr_r) *
         * lambda(x)
         */
        for (i = 0; i <= NROOTS; i++)
          b[i] = (lambda[i] == 0) ? AO : mod255(INDEX_OF1[lambda[i]] - discr_r + NN);
      } 
      else {
        /* 2 lines below: B(x) <-- x*B(x) */
        memmove(&b[1],b,NROOTS*sizeof(b[0]));
        b[0] = AO;
      }
      memcpy(lambda,t,(NROOTS+1)*sizeof(t[0]));
    }
  }

  /* Convert lambda to index form and compute deg(lambda(x)) */
  deg_lambda = 0;
  for(i=0;i<NROOTS+1;i++){
    lambda[i] = INDEX_OF1[lambda[i]];
    if(lambda[i] != AO)
      deg_lambda = i;
  }
  /* Find roots of the error+erasure locator polynomial by Chien search */
  memcpy(&reg[1],&lambda[1],NROOTS*sizeof(reg[0]));
  count = 0;            /* Number of roots of lambda(x) */
  for (i = 1,k=IPRIM-1; i <= NN; i++,k = mod255(k+IPRIM)) {
    q = 1; /* lambda[0] is always 0 */
    for (j = deg_lambda; j > 0; j--){
      if (reg[j] != AO) {
        reg[j] = mod255(reg[j] + j);
        q ^= ALPHA_TO1[reg[j]];
      }
    }
    if (q != 0)
      continue; /* Not a root */
    /* store root (index-form) and error location number */
    root[count] = i;
    loc[count] = k;
    /* If we've already found max possible roots,
     * abort the search to save time
     */
    if(++count == deg_lambda)
      break;
  }
  if (deg_lambda != count) {
    /*
     * deg(lambda) unequal to number of roots => uncorrectable
     * error detected
     */
    count = -1;
    goto finish;
  }
  /*
   * Compute err+eras evaluator poly omega(x) = s(x)*lambda(x) (modulo
   * x**NROOTS). in index form. Also find deg(omega).
   */
  deg_omega = 0;
  for (i = 0; i < NROOTS;i++){
    tmp = 0;
    j = (deg_lambda < i) ? deg_lambda : i;
    for(;j >= 0; j--){
      if ((s[i - j] != AO) && (lambda[j] != AO))
        tmp ^= ALPHA_TO1[mod255(s[i - j] + lambda[j])];
    }
    if(tmp != 0)
      deg_omega = i;
    omega[i] = INDEX_OF1[tmp];
  }
  omega[NROOTS] = AO;

  /*
   * Compute error values in poly-form. num1 = omega(inv(X(l))), num2 =
   * inv(X(l))**(FCR-1) and den = lambda_pr(inv(X(l))) all in poly-form
   */
  for (j = count-1; j >=0; j--) {
    num1 = 0;
    for (i = deg_omega; i >= 0; i--) {
      if (omega[i] != AO)
        num1  ^= ALPHA_TO1[mod255(omega[i] + i * root[j])];
    }
    num2 = ALPHA_TO1[mod255(root[j] * (FCR - 1) + NN)];
    den = 0;

    /* lambda[i+1] for i even is the formal derivative lambda_pr of lambda[i] */
    for (i = min1(deg_lambda,NROOTS-1) & ~1; i >= 0; i -=2) {
      if(lambda[i+1] != AO)
        den ^= ALPHA_TO1[mod255(lambda[i+1] + i * root[j])];
    }
    if (den == 0) {
      count = -1;
      goto finish;
    }
    /* Apply error to data */
    if (num1 != 0) {
      data[loc[j]] ^= ALPHA_TO1[mod255(INDEX_OF1[num1] + INDEX_OF1[num2] + NN - INDEX_OF1[den])];
    }
  }
finish:
  if(eras_pos != NULL){
    for(i=0;i<count;i++)
      eras_pos[i] = loc[i];
  }
  return count;
}

/*int tbchs::parity(int x){
 
  x ^= (x >> 16);
  x ^= (x >> 8);
  return x;
}*/
int tbchs::parity(int x){
  x ^= x >> 4;
  x ^= x >> 2;
  x ^= x >> 1;
  return x & 1;
}


void tbchs::init_sync(){
  int sr,i;

  sr = 0x7f;
  for(i=0;i<COLUMNS;i++){
    Sync_vector[i] = (sr & 64) ? 1 : 0;
    sr = (sr << 1) | parity(sr & PNPOLY);
  }
}
long long tbchs::sumsq_wq(unsigned char *in,int cnt){
  long long sum = 0;
  int i;

  for(i=0;i<cnt;i++){
    sum += (long)in[i] * in[i];
  }
  return sum;
}




/*void loop()
{
  

 
  init_test();
  delay(5000);
  reset_encoder1();
  //init_encoder1();
   for(int i=0;i<256;i++){
    encode_byte1(RSindata[i]);
   }
}
*/
void tbchs::bitinwithGCFEC(int bitin)
{
 

  switch (CodeState)
  {
  default:
  case HUNT:   
    if(getData1((byte)bitin) == 2){
      CodeState = DETECTED;
      
    }
    cntfec=0;
    break;

  case DETECTED:
      byte tbyte = byte(bitin);
      raw[cntfec++]=tbyte<<7;
      if (cntfec==5200){
        decodeAO40bit(1);
      
     
      CodeState= HUNT;
      cntfec=0;
      }
  }

}


void tbchs::decodeAO40bit(unsigned char decoderbyte){
  int index;
   fecmetriccnt = (fecmetriccnt+1)% 256;
   raw[rp]=decoderbyte<<7;
   //energy = sumsq_wq(raw,5200);
  
  //energy += (int)raw[rp] * raw[rp];
  rp = (rp+1) % SYMPBLOCK;
//  rp=0;
    /* Run the sync correlator */
   
    corr_amp = 0;
    for(int j=0;j<COLUMNS;j++){

      index = (rp + j*ROWS) % 5200;
	  //  if(raw[index]==0x80) put_rx_char('1');else put_rx_char('0');
    // corr_amp += Sync_vector[j]<<7 ? raw[index]: -raw[index];
	    if(Sync_vector[j]==raw[index]>>7){
			corr_amp++;
			// put_rx_char('+');
		}
		else {corr_amp--;
		   //  put_rx_char('-');
		}
       
     // Serial.print(raw[index]);
      // Serial.print(" ");
    }
	
		
		  

    /* See if the correlator peak is strong enough to be worth trying a decode
     * It's best to use a lower threshold as no harm will come from an
     * incorrect sync other than some wasted CPU time, but a higher threshold
     * may miss some real frames. This is empirical, and needs some rigor.
     */
	
    if(corr_amp<40){
//    if(corr_amp*corr_amp < 5000*energy/SYMPBLOCK) {
    // Serial.print("NCT ");
      //Serial.println(corr_amp*corr_amp);
     if(fecmetriccnt==0){
		 fecmetric--;
		 if(fecmetric<0)fecmetric=0;
		  display_metric(fecmetric);
	 }
       /* Skip ahead one symbol */
    //  energy -= (int)raw[rp] * raw[rp];
      return;
    }
    //  goto skip_symbol;
  //  Serial.println(corr_amp);
      fecmetric = corr_amp;
	  display_metric(corr_amp);

    coltop=0;
    for(col=1;col<ROWS;col++){          /* Skip first column as it's the sync vector */
      rowstart=0;
      for(row=0;row<COLUMNS;row++){
        index = (rp + rowstart+col) % 5200;
        // int index1= (rp+coltop+row)%5200;
          symbols[ coltop+row]=raw[index]; 
      //  symbols[coltop+row]=raw[rowstart+col];  /* coltop=col*65 ; rowstart=row*80 */
        rowstart+=ROWS;
      }
      coltop+=COLUMNS;
    }
    /* end of de-interleaving */


    /* Step 2: Viterbi decoder */
    /* ----------------------- */

    /* Input  array:  symbols  */
    /* Output array:  vitdecdata */
    viterbi27(vitdecdata,symbols,NBITS);


    /* Steps 3: RS decoder */
    /* ------------------- */

    /* There are two RS decoders, processing 128 bytes each.
     *
     * If both RS decoders are SUCCESSFUL
     * On exit:
     *   rs_failures = 0
     *   rserrs[x]   = number of errors corrected;  range 0 to 16   (x= 0 or 1)
     *   Data output is in array RSdecdata[256].
     *
     * If an RS decoder FAILS
     * On exit:
     *   rs_failures = 1 or 2   (i.e. != 0)
     *   rserrs[x] contains -1
     *   Data output should not be used.
     */


    /* Input  array:  vitdecdata */
    /* Output array:  RSdecdata  */

    char rsblocks[RSBLOCKS][NN];          /*  [2][255] */
    int di,si;                            //row col
    int rs_failures ;                     /* Flag set if errors found */
    int rserrs[RSBLOCKS];                 /* Count of errors in each RS codeword */

    //FILE *fp ;                            /* Needed if you save o/p to file */

    /* Interleave into Reed Solomon codeblocks */
    memset(rsblocks,0,sizeof(rsblocks));                          /* Zero rsblocks array */
    di = 0;
    si = 0;
    for(col=RSPAD;col<NN;col++){
      for(row=0;row<RSBLOCKS;row++){
        rsblocks[row][col] = vitdecdata[di++] ^ Scrambler[si++];  /* Remove scrambling */
      }
    }
    /* Run RS-decoder(s) */
    rs_failures = 0;
    for(row=0;row<RSBLOCKS;row++){
      rserrs[row] = decode_rs_8_fec(rsblocks[row],NULL,0);
      rs_failures += (rserrs[row] == -1);
    }

    /* If frame decoded OK, deinterleave data from RS codeword(s), and save file */
   // Serial.print("RSF ");
  //  for(int j=0;j<256;j++)  Serial.print(RSdecdata[j]);
    
   
    if(!rs_failures){
     
      // memset(raw,0,5200);
      
         // for(int j=0;j<256;j++) 
          
       
       //  memset(vitdecdata,0,(NBITS-6)/8);
       //  memset(symbols,0,5200);
         //rp=0;
       // energy=0;
     // rp=0;
   
      int j = 0;

      for(col=RSPAD;col<KK;col++){
        for(row=0;row<RSBLOCKS;row++){
          RSdecdata[j++] = rsblocks[row][col];
        
         // Serial.println(RSdecdata[j]);
        }
      }
      /* and save out succesfully RS-decoded data */
      //fp=fopen("RSdecdataC","wb");                       /* Output 256 bytes of user's data */
      //fwrite(RSdecdata,1,sizeof(RSdecdata),fp);
      //fclose(fp);
	  storeandisplayFECdata(RSdecdata);
    }

    /* Print RS-decode status summary */
    if(Verbose){
      //delay(10000);

      //delay(20000);
      for(row=0;row<RSBLOCKS;row++){
        if(rserrs[row] != -1){
		
         // Serial.print("RS errors");
         // Serial.println(rserrs[row]);         
        }
        else{
			
       //   Serial.println("FAIL ");
         // delay(2000);
        }
		char msg[80];
		int rscorr = rserrs[0]+rserrs[1];
	    snprintf(msg, sizeof(msg), "RSCorr %d", rscorr);
	    put_Status2(msg);

      }
    }
    /* end of rs section */

   
    //skip_symbol:
    //   Serial.println("skipped a symbol");
    // delay(3000);
    /* Skip ahead one symbol */
     // energy -= (int)raw[rp] * raw[rp];
    //fread(&symbols[rp],sizeof(symbols[rp]),1,stdin); //get a byte of data here.
    //    energy += (int)raw[rp] * raw[rp];
    //   rp = (rp+1) % SYMPBLOCK;
  


}   /*end of main*/


