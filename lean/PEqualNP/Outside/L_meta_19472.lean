import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19472 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (11911415 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.or, [8, 2]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.and, [7, 10]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.not, [17]⟩,
    ⟨.or, [14, 18]⟩], 19⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
