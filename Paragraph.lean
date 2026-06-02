import Lean
import Qq
open Lean Qq

namespace Lean.MessageData

inductive ParagraphElement
  /--
  An unbreakable chunk of text
  -/
  | text (s : String)

  /--
  An inline message. May actually turn out not inline when it would not fit.
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

instance: Append Paragraph := ⟨List.append⟩
instance: HAppend ParagraphElement ParagraphElement Paragraph := ⟨([·,·])⟩
instance: HAppend ParagraphElement Paragraph Paragraph := ⟨List.cons⟩
instance: HAppend Paragraph ParagraphElement Paragraph := ⟨List.concat⟩

/--
Turn a `String` into a `Paragraph` by turning any whitespace into soft line
breaks
-/
def Paragraph.ofString (s : String) : Paragraph := Id.run do
  let mut l : List ParagraphElement :=
    (s.split Char.isWhitespace).toList
    |>.filter (not ·.isEmpty)
    |>.map (.text ·.copy)
    |> join
  if s.startsWith Char.isWhitespace then l := .line :: l
  if s.endsWith   Char.isWhitespace then l := l.concat .line
  return l
where
  join : List ParagraphElement → List ParagraphElement
    | [] => []
    | [e] => [e]
    | e::es => e :: .line :: join es

/--
Turn a `String` into a `Paragraph` as a single unbreakable thing
-/
def Paragraph.ofStringNoWrap : String → Paragraph := ([.text ·])

macro:max "pm!" s:interpolatedStr(term) : term => do
  s.expandInterpolatedStr (← `(Paragraph))
    (ofInterpFn :=← `(ParagraphElement.inline))
    (ofLitFn :=← `(Paragraph.ofString))

end Lean.MessageData
