import Lean
import Qq
open Lean Qq

namespace Lean.MessageData

/--
Turn `MessageData` into `Format` in `MetaM`.

With just `MessageData.format` and no context, `MessageData.ofExpr` (aka
`ToMessageData Expr`) uses `toString`.
-/
def format' (msg : MessageData) : MetaM Format := do
  msg.format (ctx? := some ⟨← getEnv, ← getMCtx, ← getLCtx, ← getOptions⟩)

inductive ParagraphElement
  /--
  An unbreakable chunk of text
  -/
  | text (s : String)

  /--
  An inline message. May actually turn out not inline when it would not fit. An
  inline message always has an implicit soft break already at the start, but
  none at the end, just like, and for the same reasons as `Lean.indentD` has an
  `Std.Format.line` at the beginning, but not at the end.
  -/
  | inline (m : MessageData)

  /--
  A soft line break
  -/
  | line

def Paragraph := List ParagraphElement

/--
Normalize soft breaks: collapse multiple soft breaks into single ones, strip
leading and trailing ones.
-/
def Paragraph.normalize (p : Paragraph) : Paragraph :=
  match loop p with
    | .line :: es => es
    | es => es
where
  loop : Paragraph → Paragraph
    | []                        => []
    | [.line]                   => []
    | .line :: .line :: es      => loop (.line :: es)
    -- | .line :: .inline m :: es  => loop (.inline m :: es)
    | e :: es                   => e :: loop es

def ofParagraph (p : Paragraph) : MessageData :=
  let m := p.normalize.foldl (init := .nil) (· ++ match · with
    | .text s => .ofFormat (.text s)
    | .inline m => m
    | .line => .ofFormat .line)
  .fill m
-- where
  -- inline : MessageData → MessageData := indentD ∘ group

instance: Append Paragraph := ⟨List.append⟩
instance: HAppend ParagraphElement ParagraphElement Paragraph := ⟨([·,·])⟩
instance: HAppend ParagraphElement Paragraph Paragraph := ⟨List.cons⟩
instance: HAppend Paragraph ParagraphElement Paragraph := ⟨List.concat⟩

/--
Turn a `String` into a `Paragraph` by turning any whitespace into soft line
breaks
-/
def Paragraph.ofString (s : String) : Paragraph :=
  let l : List ParagraphElement :=
    (s.split Char.isWhitespace).toList
    |>.filter (not ·.isEmpty)
    |>.map (.text ·.copy)
    |>.foldl (init := []) (· ++ [·, .line])
  if s.startsWith Char.isWhitespace
  then .line :: l else l

/--
Turn a `String` into a `Paragraph` as a single unbreakable thing
-/
def Paragraph.ofStringNoWrap : String → Paragraph := ([.text ·])

macro:max "pm!" s:interpolatedStr(term) : term => do
  s.expandInterpolatedStr (← `(Paragraph))
    (ofInterpFn :=← `(ParagraphElement.inline))
    (ofLitFn :=← `(Paragraph.ofString))

end Lean.MessageData
