import MPiL.Util
import W.Syntax
open Lean Std Format

#check Format

namespace Hidden
inductive Format where
  | nil                 : Format
  | line                : Format
  | align (force : Bool) : Format
  | text                : String → Format
  | nest (indent : Int) (f : Format) : Format
  | append : Format → Format → Format
  | group : Format → (behavior : FlattenBehavior := FlattenBehavior.allOrNone) → Format
  | tag : Nat → Format → Format
end Hidden

variable {α : Type u} [ToFormat α]

def List.f1 (xs : List α) : Format :=
  group (behavior := .fill) <|
    nest 2 (text "(" ++ line ++ joinSep xs line) ++
    line ++
    ")"

#check bracket
#check List.format

run_meta logInfo <| (List.range 20).format.pretty 10
run_meta logInfo <| (List.range 20).f1.pretty 10 4


-- TODO: Understand align (force := true)

-- TODO: nest, (initial indent), and the first line; how to start indented from the start?; bug?

-- macro id:ident " :++= " t:term : doElem => `(doElem| $id:ident := $id ++ $t)

def List.f2 (xs : List α) : Format := Id.run do
  let mut fmt : Format := .nil
  fmt :++= "a"
  ("a" ++ · : Format → Format) <| group (behavior := .fill) <|
    "a" ++ nest 2 (line ++ joinSep xs line ++ line)

run_meta logInfo <| (List.range 20).f2.pretty 10 4

def Std.Format.joinWithSoftBreaks (fs : List Format) : Format :=
  .joinSep fs .line

run_meta
  let f : Format := .group (behavior := .fill) <|
      "a" ++
      (.nest 2 <| .group (.line ++ "x\ny")) ++ .line ++
      "b"
  logInfo f
