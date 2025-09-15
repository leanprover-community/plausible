import Lean
open Lean

/-- Option to enable debug messages from Chamelean -/
register_option chamelean.debug : Bool := {
  defValue := false
  group := "chamelean"
  descr := "enable debug messages from Chamelean"
}

/-- Global flag for enabling/diabling debug messages -/
def globalDebugFlag : Bool := false

/-- Determines whether the `chamelean.debug` Option flag is set -/
def inDebugMode [Monad m] [MonadOptions m] : m Bool := do
  let opts ← getOptions
  return Lean.Option.get opts chamelean.debug

/-- Performs a monadic `action` if a flag value is set -/
def withDebugFlag [Monad m] [MonadOptions m] [MonadWithOptions m] [MonadLog m] [AddMessageContext m] (flag : Bool) (action : m Unit) : m Unit := do
  withOptions (fun opts => opts.set `chamelean.debug flag) do
    if (← inDebugMode) then do
      action
      logInfo ""
