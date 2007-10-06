//
// "$Id: threads.h 4748 2006-01-15 02:26:54Z mike $"
//
// Simple threading API for the Fast Light Tool Kit (FLTK).
//
// Copyright 1998-2006 by Bill Spitzak and others.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Library General Public
// License as published by the Free Software Foundation; either
// version 2 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Library General Public License for more details.
//
// You should have received a copy of the GNU Library General Public
// License along with this library; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
// USA.
//
// Please report all bugs and problems on the following page:
//
//     http://www.fltk.org/str.php
//

// Inline classes to provide portable support for threads and mutexes.
//
// FLTK does not use this (it has an internal mutex implementation
// that is used if Fl::lock() is called). This header file's only
// purpose is so we can write portable demo programs. It may be useful
// or an inspiration to people who want to try writing multithreaded
// programs themselves.
//
// FLTK has no multithreaded support unless the main thread calls Fl::lock().
// This main thread is the only thread allowed to call Fl::run() or Fl::wait().
// From then on FLTK will be locked except when the main thread is actually
// waiting for events from the user. Other threads must call Fl::lock() and
// Fl::unlock() to surround calls to FLTK (such as to change widgets or
// redraw them).

#ifndef Threads_H
#  define Threads_H

#ifndef WIN32
// Use POSIX threading...

#    include <pthread.h>

typedef pthread_t			Fl_Thread;
typedef pthread_mutex_t		Fl_Mutex;
typedef pthread_cond_t		Fl_Cond;

extern int fl_create_thread(Fl_Thread & t, void *(*f)(void *), void* p);
extern int fl_mutex_init(Fl_Mutex * m);
extern int fl_cond_init(Fl_Cond * c);
extern int fl_cond_wait(Fl_Cond *c, Fl_Mutex *m);
extern int fl_cond_signal(Fl_Cond *c);
extern int fl_lock(Fl_Mutex *m);
extern int fl_unlock(Fl_Mutex *m);
extern int fl_join(Fl_Thread t);

#else

#    include <windows.h>
#    include <process.h>

typedef unsigned long Fl_Thread;
extern int fl_create_thread(Fl_Thread * t, void *(*f) (void *), void* p);

#  endif // !WIN32

// we have 4 threads, only 3 of which will use qrunner
enum { UNKNOWN_TID = -1, TRX_TID, QRZ_TID, RIGCTL_TID, FLMAIN_TID,
       NUM_THREADS, NUM_QRUNNER_THREADS = NUM_THREADS - 1 };

#if (USE_TLS == 1)
	extern __thread int thread_id_;
#	define CREATE_THREAD_ID() thread_id_ = UNKNOWN_TID
#	define SET_THREAD_ID(x)   thread_id_ = (x)
#	define GET_THREAD_ID()    thread_id_
#else
#	ifdef WIN32 // assume no pthreads support
#		error need TLS support
#	endif
	extern pthread_key_t thread_id_;
#	define CREATE_THREAD_ID() pthread_key_create(&thread_id_, 0);
#	define SET_THREAD_ID(x)   pthread_setspecific(thread_id_, (void *)(x))
#	define GET_THREAD_ID()    (int)pthread_getspecific(thread_id_)
#endif // (USE_TLS == 1)

#include "fl_lock.h"

#endif // !Threads_h

//
// End of "$Id: threads.h 4748 2006-01-15 02:26:54Z mike $".
//
