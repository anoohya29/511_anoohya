

import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {P Q R : Prop} (h₁ : P ∧ Q → R) : P → (Q → R) :=
begin
  intro hP,
  intro hQ,
  have hPQ : P ∧ Q := And.intro hP hQ,
  have hR : R := h₁ hPQ,
  exact hR,
end

