import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4825_2
    (hAnd : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (C : Circuit),
      n < E.card →
      (∀ p q l s : Fin n, p ≠ q → l ≠ s →
        ¬((p, l) ∈ E ∧ (p, s) ∈ E ∧ (q, l) ∈ E ∧ (q, s) ∈ E)) →
      (∀ p : Fin n, (p, σ p) ∈ E) →
      IsAO2 (n + n) C →
      (∀ z : Fin (n + n) → Bool, circuitFun (n + n) C z =
        decide (∃ p l : Fin n, (p, l) ∈ E ∧ z (Fin.castAdd n p) = true ∧
          z (Fin.natAdd n l) = true)) →
      C.output + (1 : ℕ) = n + n + C.size →
      (List.flatMap Gate.inputs C.gates).toFinset = Finset.range (n + n + C.size - (1 : ℕ)) →
      ∃ f : Fin n → Fin C.gates.length, Function.Injective f ∧
        ∀ i, (C.gates.get (f i)).op = GateOp.and)
    (hOr : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (C : Circuit),
      n < E.card →
      (∀ p q l s : Fin n, p ≠ q → l ≠ s →
        ¬((p, l) ∈ E ∧ (p, s) ∈ E ∧ (q, l) ∈ E ∧ (q, s) ∈ E)) →
      (∀ p : Fin n, (p, σ p) ∈ E) →
      IsAO2 (n + n) C →
      (∀ z : Fin (n + n) → Bool, circuitFun (n + n) C z =
        decide (∃ p l : Fin n, (p, l) ∈ E ∧ z (Fin.castAdd n p) = true ∧
          z (Fin.natAdd n l) = true)) →
      C.output + (1 : ℕ) = n + n + C.size →
      (List.flatMap Gate.inputs C.gates).toFinset = Finset.range (n + n + C.size - (1 : ℕ)) →
      ∃ f : Fin (E.card - 1) → Fin C.gates.length, Function.Injective f ∧
        ∀ i, (C.gates.get (f i)).op = GateOp.or) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x6 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 x6 = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x1), (x7, x8) ∈ x2 ∧ x6 (Fin.castAdd x1 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true);   x1 < x2.card → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → x5 x4 → x4.output + (1 : ℕ) = x1 + x1 + x4.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates).toFinset = Finset.range (x1 + x1 + x4.size - (1 : ℕ)) → x2.card - x1 ≤ (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates).toFinset.card := by
  intro n E σ C computes hlt hrect hmatch hAO heval hlast hcover
  obtain ⟨fA, hfAinj, hfAop⟩ := hAnd n E σ C hlt hrect hmatch hAO heval hlast hcover
  obtain ⟨fO, hfOinj, hfOop⟩ := hOr n E σ C hlt hrect hmatch hAO heval hlast hcover
  have hdis : ∀ a : Fin n, ∀ b : Fin (E.card - 1), fA a ≠ fO b := by
    intro a b h
    have hop : GateOp.and = GateOp.or := by
      have hg : C.gates.get (fA a) = C.gates.get (fO b) := congrArg C.gates.get h
      rw [← hfAop a, hg, hfOop b]
    cases hop
  let idx : Fin n ⊕ Fin (E.card - 1) → Fin C.gates.length := Sum.elim fA fO
  have hidx : Function.Injective idx := by
    intro u v huv
    cases u with
    | inl a =>
      cases v with
      | inl c =>
        exact congrArg Sum.inl (hfAinj (by simpa [idx] using huv))
      | inr b =>
        have hab : fA a = fO b := by simpa [idx] using huv
        exact (hdis a b hab).elim
    | inr b =>
      cases v with
      | inl a =>
        have hba : fO b = fA a := by simpa [idx] using huv
        exact (hdis a b hba.symm).elim
      | inr d =>
        exact congrArg Sum.inr (hfOinj (by simpa [idx] using huv))
  have hsize : E.card + n ≤ C.size + 1 := by
    have himg := Finset.card_image_of_injective (Finset.univ : Finset (Fin n ⊕ Fin (E.card - 1))) hidx
    have huniv : (Finset.univ : Finset (Fin n ⊕ Fin (E.card - 1))).card = n + (E.card - 1) := by
      rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have hle : (Finset.univ.image idx).card ≤ C.gates.length := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (Finset.univ.image idx)
    have hcard : n + (E.card - 1) ≤ C.size := by
      have hle' : n + (E.card - 1) ≤ C.gates.length := by
        simpa [himg, huniv] using hle
      rwa [show C.gates.length = C.size from rfl] at hle'
    omega
  have hfan : ∀ g ∈ C.gates, g.inputs.length = 2 := by
    unfold IsAO2 at hAO
    exact hAO.2.2
  have hlenAll : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length = 2) →
      (gs.flatMap Gate.inputs).length = 2 * gs.length := by
    intro gs
    induction gs with
    | nil =>
      intro _
      simp
    | cons g gs ih =>
      intro h
      have hg : g.inputs.length = 2 := h g (by simp)
      have hrest : (gs.flatMap Gate.inputs).length = 2 * gs.length :=
        ih (fun x hx => h x (by simp [hx]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have hlen : (List.flatMap Gate.inputs C.gates).length = 2 * C.size := by
    have h := hlenAll C.gates hfan
    have hsz : C.gates.length = C.size := rfl
    rw [hsz] at h
    simpa using h
  have hcard : (C.gates.flatMap Gate.inputs).toFinset.card = n + n + C.size - 1 := by
    rw [hcover]
    exact Finset.card_range _
  omega
