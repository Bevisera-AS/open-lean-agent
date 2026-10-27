module

namespace LeanAgent

public section

/-- True when `s` contains a non-whitespace character. Stated over the
character list so the kernel can decide it on literals (`String.any` cannot be
reduced by `decide` on this toolchain). -/
@[expose] public def nonemptyText (s : String) : Bool :=
  s.toList.any fun c => !c.isWhitespace

public def joinSep (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinSep sep xs

end

end LeanAgent
