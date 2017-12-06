{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}
module Trace where

import Control.DeepSeq
import Debug.Trace
import Debug.NoTrace


tracef :: String -> a -> a
tracef !x y = (\ !x y -> y) (force x) y


tracep = Debug.Trace.trace

tracesafe = Debug.NoTrace.trace


#define NOTRACE 2
#if NOTRACE == 1
trace = tracef 
#elif NOTRACE == 0
trace = tracep
#else
trace = tracesafe
#endif