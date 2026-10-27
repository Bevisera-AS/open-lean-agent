import BuildOk

def main : IO UInt32 := do
  unless BuildOk.double 21 == 42 do
    IO.eprintln "double is wrong"
    return 1
  IO.println "build-ok tests passed"
  return 0
