def Array.findIdxFrom? (a : Array α) (start : Nat) (p : α → Bool) : Option Nat := Id.run do
  for h : i in [start:a.size] do
    have : i < a.size := h.upper
    if p a[i] then
      return i
  return none

partial def Array.collectParts (a : Array α) (p : α → Bool) : Array (Array α) := Id.run do
  let mut result := #[]
  let mut a := a
  repeat
    if let some idx := a.findIdxFrom? 1 p then
      result := result.push <| a.extract 0 idx
      a := a.extract idx a.size
    else
      result := result.push a
      break
  return result

def Array.flatten (a : Array (Array α)) : Array α :=
  a.foldl (init := #[]) (· ++ ·)

-- ↑ Utils ↑
namespace Lean.Linter.PrettyPrinter

/- Specifies the behavior when the flattened group does not fit the line. -/
inductive GroupBehavior
  /- Turn all separators into line breaks. -/
  | uniform
  /- Turn the last fitting separator into a line break and continue with the rest of the group. -/
  | fill
  deriving Repr

instance : ToString GroupBehavior where
  toString
  | .uniform => "uniform"
  | .fill => "fill"

inductive Format
  /- Empty format. -/
  | nil
  /- Text `s`. -/
  | text (s : String)
  /- Formats `a` and `b` next to each other. -/
  | append (a b : Format)
  /- Separator string `s`, replaced with a hard line break if necessary. -/
  | sep (s : String)
  /- Increase the nesting depth in `fmt` by `indent`. -/
  | nest (indent : Int) (fmt : Format)
  /- Flatten `fmt` if possible and resolve conflicts according to `behavior`. -/
  | group (fmt : Format) (behavior : GroupBehavior := .uniform)
  deriving Inhabited

private inductive ResolvedFormat
  /- Empty format. -/
  | nil
  /- Hard line break with indent `indent`. -/
  | line (indent : Nat)
  /- Text `s`; may not contain `\n`. -/
  | text (s : String)
  /- Formats `a` and `b` next to each other. -/
  | append (a b : ResolvedFormat)
  /- Separator string `s`, replaced with `.line indent` if necessary. -/
  | sep (s : String) (indent : Nat)
  /- Flatten all `fmts` if possible and resolve conflicts according to `behavior`. -/
  | group (behavior : GroupBehavior) (fmts : Array ResolvedFormat)
  deriving Inhabited, Repr

private partial def resolvedFormatToString : ResolvedFormat → String
  | .nil => "nil"
  | .line indent => s!"(line {indent})"
  | .text s => s!"(text \"{s}\")"
  | .append a b => s!"(append {resolvedFormatToString a} {resolvedFormatToString b})"
  | .sep s indent => s!"(sep \"{s}\" {indent})"
  | .group behavior fmts => s!"(group {behavior} {fmts.map resolvedFormatToString})"

instance : ToString ResolvedFormat where
  toString := resolvedFormatToString

partial def Format.resolve (indent : Int := 0) : Format → ResolvedFormat
  | .nil                     => .nil
  | .text s                  => s |>.split (· == '\n') |>.map .text |>.intersperse (.line indent.toNat) |> appendAll
  | .append a b              => .append (resolve indent a) (resolve indent b)
  | .sep s                   => .sep s indent.toNat
  | .nest indentIncrease fmt => resolve (indent + indentIncrease) fmt
  | .group fmt behavior      => .group behavior (collectFmts <| resolve indent fmt)
where
  appendAll (fmts : List ResolvedFormat) : ResolvedFormat :=
    fmts.foldr (init := .nil) .append
  collectFmts : ResolvedFormat → Array ResolvedFormat
    | .append a b => collectFmts a ++ collectFmts b
    | .nil        => #[]
    | fmt         => #[fmt]

-- measurement work on `ResolvedFormat`
private structure MeasureState where
  currColumn : Nat
  width : Nat

/- Measure the length of the given format, but stop when the current line is exceeded.
Requires `currentColumn` to be less than `width`. -/
private partial def measureFlatUpToWidth : ResolvedFormat → StateM MeasureState Unit
  | .nil =>
    pure ()
  | .line indent =>
    modify fun st => { st with currColumn := indent }
  | .text s =>
    modify fun st => { st with currColumn := st.currColumn + s.length }

  | .append a b => do
    measureFlatUpToWidth a
    if (← get).currColumn < (← get).width then
      measureFlatUpToWidth b
  | .sep s _ =>
    measureFlatUpToWidth <| .text s
  | .group _ fmts => do
    for fmt in fmts do
      measureFlatUpToWidth fmt
      if (← get).currColumn ≥ (← get).width then
        break

/- Fit as many parts on the current line as possible and return them together with the remaining parts. -/
private def fillLine (currColumn : Nat) (width : Nat) (parts : Array (Array ResolvedFormat)) : Array (Array ResolvedFormat) × Array (Array ResolvedFormat) :=
  if currColumn ≥ width then
    (#[], parts)
  else
    go |>.run { currColumn, width } |>.1
where
  go : StateM MeasureState <| Array (Array ResolvedFormat) × Array (Array ResolvedFormat) := do
    let mut line := #[]
    for (i, part) in parts.mapIdx (·, ·) do
      -- measure whether the next part fits on the current line
      measureFlatUpToWidth <| .group .uniform part

      if (← get).currColumn < (← get).width then
        -- if so, append it to the current line and continue
        line := line.push part
      else
        -- otherwise finish the current line and return the remaining parts as rest
        return (line, parts.extract i parts.size)

    return (line, #[])

-- pretty printing of `ResolvedFormat`
class PrettyMonad (m : Type → Type) where
  pushNewline (indent : Nat) : m Unit
  pushText (s : String) : m Unit
  currColumn : m Nat
open PrettyMonad

private partial def prettyM [Monad m] [PrettyMonad m] (width : Nat) (flatten : Bool) : ResolvedFormat → m Unit
  | .nil         => pure ()
  | .line indent => pushNewline indent
  | .text s      => pushText s

  | .append a b => do
    prettyM width flatten a
    prettyM width flatten b
  | .sep s indent => do
    -- whether separators are flattened is decided on the group level
    if flatten then
      pushText s
    else
      pushNewline indent

  | .group behavior fmts => do
    if flatten then
      -- we already know that the entire flattened group wil fit in the current line
      for fmt in fmts do
        prettyM width true fmt
    else
      -- make sure the group is non-empty
      if fmts.isEmpty then
        return ()

      -- split the group in parts that can be placed on different lines
      let parts := fmts.collectParts (fun fmt => fmt matches .sep _ _ || fmt matches .line _)

      -- try to fit as many parts of the flattened group in the current line
      let (line, rest) := fillLine (← currColumn) width parts
      if rest.isEmpty then
        -- entire group fits
        for fmt in fmts do
          prettyM width true fmt
      else
        -- only some parts of the group fit
        match behavior with
        | .uniform =>
          -- do not flatten any separators
          for fmt in fmts do
            prettyM width false fmt
        | .fill =>
          if line.isEmpty then
            -- try to fit the first part by breaking deeper separators
            -- remember that `part` does not contain any `.sep`s
            let part := parts[0]!
            for (i, fmt) in part.mapIdx (·, ·) do
              if let .group behavior fmts := fmt then
                -- make the group account for the remaining formats when deciding to flatten `sep`s
                prettyM width false <| .group behavior <| fmts ++ (part.extract (i + 1) part.size)
                break
              else
                prettyM width false fmt

            -- continue with the rest of the group
            for fmt in (parts.extract 1 parts.size).flatten do
              prettyM width false fmt
          else
            -- flatten the parts of the group that fit in the current line
            for fmt in line.flatten do
              prettyM width true fmt

            let rest := rest.flatten
            -- insert a line break (from `.sep` or `.line`)
            prettyM width false rest[0]!
            -- continue with the rest of the group
            prettyM width false <| .group behavior (rest.extract 1 rest.size)

-- default instances for `PrettyMonad`
structure StringPrettyState where
  out : String := ""
  currColumn : Nat := 0

instance : PrettyMonad <| StateM StringPrettyState where
  pushNewline indent := modify fun st =>
    let indentChars := List.replicate indent ' '
    { st with
      out := st.out ++ "\n" ++ String.mk indentChars
      currColumn := indent }
  pushText s := modify fun st =>
    { st with
      out := st.out ++ s
      currColumn := st.currColumn + s.length }
  currColumn := do return (← get).currColumn

-- convenience methods
def pretty (fmt : Format) (width : Nat) : String :=
  (prettyM width false fmt.resolve : StateM StringPrettyState Unit) |>.run {} |>.run |>.2.out
