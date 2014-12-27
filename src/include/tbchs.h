// ----------------------------------------------------------------------------
// tbchs.h  --  tbchs MODEM
//
// Copyright (C) 2006
//		Dave Freese, W1HKJ
//
// This file is part of fldigi.
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

#ifndef _tbchs_H
#define _tbchs_H

#include "trx.h"
#include <iostream>
#include "complex.h"
#include "modem.h"
#include "globals.h"
#include "filters.h"
#include "fftfilt.h"
#include "digiscope.h"
#include <string.h>
#include <cstring>
#define	tbchs_SampleRate	48000
#define	SYMLEN			512
#define tbchs_BW		100

#define BUFFLEN			4096
#define SCOPE_DATA_LEN	1024
#define MAXPIPE			1024

// lp filter
//#define	DEC_1		8		
//#define FIRLEN_1	256
//#define BW_1		10

// NASA coefficients for viterbi encode/decode algorithms
//#define	K	7
//#define	POLY1	0x6d
//#define	POLY2	0x4f


class tbchs : public modem {
protected:
	double			phaseacc;
	double			phaseincr;

	C_FIR_filter	*bandpass;
	C_FIR_filter	*lowpass;
	C_FIR_filter	*hilbert;
	Cmovavg			*moving_avg;
	sfft			*slidingfft;

	int				symlen;
// receive
	double			*scope_data;
	double			*inbuf;
	inline cmplx mixer(cmplx in,double f);
// transmit
	int txstate;

	double			*outbuf;
	unsigned int	buffptr;

private:
	int decodeGold1( uint64_t keycode);
	void initmatchedfilter();
	int32_t demodulate(int16_t input);
	void decode(int16_t inbyte);
	int32_t runFiltAverager(int32_t datain);
	int getData10(byte bitin);
	int getData1(byte bitin);
	void bitinwithGC(int bitin);
	void deshuffle(byte *rxbuf);
	void deinterleaver1();
	uint16_t crtty_CRC16_checksum (char rxByte[],int length);
	void checksum_crc16_ccitt();
	double *pipe;
	double *dsppipe;
	int pipeptr;
	int inp_ptr;
	int viterbi27(
    unsigned char *data,          /* Decoded output data */
    unsigned char *symbols,       /* Raw deinterleaved input symbols */
    unsigned int nbits );   
	int decode_rs_8_fec(char *data, int *eras_pos, int no_eras);
	int mod255(int x);
     int parity(int x);
	//void init_sync();
	long long sumsq_wq(unsigned char *in,int cnt);
	//void decodeAO40bit(unsigned char decoderbyte);
	void bitinwithGCFEC(int bitin);
	void storeandisplayFECdata(byte* rxByte);

public:
	tbchs();
	~tbchs();
	void	init();
	void	rx_init();
	void	tx_init(SoundBase *sc);
	void 	restart();
	int		rx_process(const double *buf, int len);
	int		tx_process();
	void	update_syncscope();
	void decodeAO40bit(unsigned char decoderbyte);
	void init_sync();
	
};

#endif
