import Lean.Elab.Command
import Lean.Linter.Util
import Lean.Linter.PrettyPrinter.PrettyPrinter

namespace Lean.Linter
open Lean.Elab.Command

private def fmtToPPFmt : Format → PrettyPrinter.Format
  | .nil                => .nil
  | .line               => .sep " "
  | .text s             => .text s
  | .nest indent fmt    => .nest indent (fmtToPPFmt fmt)
  | .append a b         => .append (fmtToPPFmt a) (fmtToPPFmt b)
  | .group fmt behavior => .group (fmtToPPFmt fmt) (behaviorToPPBehavior behavior)
  | .tag _ fmt          => fmtToPPFmt fmt
where
  behaviorToPPBehavior : Std.Format.FlattenBehavior → PrettyPrinter.GroupBehavior
    | .allOrNone => .uniform
    | .fill      => .fill


def ppTest : Linter := fun cmdStx => do
  let fmt ← liftCoreM <|
    PrettyPrinter.ppTerm (TSyntax.mk cmdStx)

  let width := 80

  let str := fmt.pretty width

  let ppFmt := fmtToPPFmt fmt
  let ppStr := PrettyPrinter.pretty ppFmt width

  if str != ppStr then
    let option : Lean.Option Bool := ⟨"prettyPrinterTest", false⟩

    -- logLint option cmdStx s!"Format:\n{PrettyPrinter.Format.resolve 0 ppFmt}"
    logLint option cmdStx s!"Lean PrettyPrinter:\n{str}"
    logLint option cmdStx s!"New PrettyPrinter:\n{ppStr}"

builtin_initialize addLinter ppTest

end Lean.Linter
