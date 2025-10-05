/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kim Morrison
-/
module

public meta import Lean.Util.Trace

public meta section

open Lean

initialize registerTraceClass `plausible.instance
initialize registerTraceClass `plausible.decoration
initialize registerTraceClass `plausible.discarded
initialize registerTraceClass `plausible.success
initialize registerTraceClass `plausible.shrink.steps
initialize registerTraceClass `plausible.shrink.candidates
