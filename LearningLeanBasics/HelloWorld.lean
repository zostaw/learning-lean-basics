/-
proof using Term Mode
-/
example (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1 )
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  Eq.trans h1 ( -- a = b
    Eq.trans h2 ( -- b = c + 1
      Eq.trans (congrArg (fun x => x + 1) h3) ( -- apply λ x: x+1 to h3 -> c + 1 = d + 1
        Eq.trans (Nat.add_comm d 1) ( -- d + 1 = 1 + d
          Eq.symm h4 -- e = 1 + d <=> 1 + d = e
        )
      )
    )
  )

/-
idiomatic way using *calc* syntax -
  *syntactic sugar* over Term Mode
-/
example (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e :=
  calc
    a = b := h1
    b = c + 1 := by rw[h2] -- rewrite b using h2: b = c + 1 -> c + 1 = c + 1
    c + 1 = d + 1 := by rw[h3]
    d + 1 = 1 + d := Nat.add_comm d 1
    1 + d = e := by rw[h4]


/-
proof using *simp*
  applies rewrite rules automaticaly
    based on list of definitions/rules
we essentially tell lean that if it combine our hypotheses and Nat.add_comm (and lemmas from library?) together, it should be able to get from a to e
-/
example (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e := by
    simp [h2, h1, h3, h4, Nat.add_comm]

/-
*simp* is a deterministic mechanism and it applies rules according
  to rules
for instance circular hypothesis' will cause an ∞ recursion
which in return will cause lean to fail after reaching max recursion depth
-/
example (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h5 : d = c) -- adding circular hypothesis breaks simp
  (h4 : e = 1 + d)
  : a = e := by
    simp [h2, h1, h3, h5, h4, Nat.add_comm]


/-
simp [*] tells simp
  to use all local hypotheses
    as rewrite rules
-/
example (a b c d e : Nat)
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d)
  : a = e := by
    simp [*, Nat.add_comm]
