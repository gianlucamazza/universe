/-
Stampa `Universe.Points.table`, una riga `chiave re im` per punto.
-/
import Universe.Points

open Universe.Points

def main : IO Unit := do
  for entry in table do
    IO.println s!"{entry.1} {entry.2.re} {entry.2.im}"
