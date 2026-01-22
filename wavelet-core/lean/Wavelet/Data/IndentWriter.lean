import Wavelet.Data.Basic

/-- A simple string writer monad with state and exception that
also records the current indentations. -/
private structure IndentWriterState (σ : Type u) where
  indent : Nat
  buf : List String
  user : σ

abbrev IndentWriterT σ ε := StateT (IndentWriterState σ) (Except ε)

namespace IndentWriterT

def writeLn (line : String) : IndentWriterT σ ε Unit :=
  modify λ s => { s with buf := s.buf ++ [String.replicateChar s.indent ' ' ++ line] }

def indentBy (n : Nat) : IndentWriterT σ ε Unit := do
  modify λ s => { s with indent := s.indent + n }

def dedentBy (n : Nat) : IndentWriterT σ ε Unit :=
  modify λ s => { s with indent := s.indent - n }

def get : IndentWriterT σ ε σ := (·.user) <$> StateT.get

def set (x : σ) : IndentWriterT σ ε Unit := do
  modify λ s => { s with user := x }

def modify (f : σ → σ) : IndentWriterT σ ε Unit := do set (f (← get))

def run (m : IndentWriterT σ ε Unit) (init : σ) : Except ε (σ × String) := do
  let (_, s) ← StateT.run m { indent := 0, buf := [], user := init }
  return ⟨s.user, String.intercalate "\n" s.buf⟩

end IndentWriterT
