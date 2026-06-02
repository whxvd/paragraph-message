import Lean
import Lean.PrettyPrinter.Formatter
import Qq
import Debug
open Lean Meta Qq
open Lean.PrettyPrinter (OneLine.pretty)

def d : Q(Id Nat) := q(do let a ← pure 0; pure (a + 0))

#check Meta.ppExpr
#check MessageData.ofExpr

run_meta
  let f ← ppExpr d
  logInfo <| repr <| OneLine.pretty f 1000000

#check Lean.PrettyPrinter.OneLine.pretty
#check Lean.Parser.prattParser

#check Std.Format.joinSep

def p := Format.line.joinSep <| List.replicate 100 "a"

run_meta logInfo <| .fill p
