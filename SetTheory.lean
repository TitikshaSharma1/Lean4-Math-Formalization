import Mathlib.Data.Set.Basic

-- Project 1: Formalizing Set Operations and De Morgan's Laws
-- Demonstrates proficiency with foundational logical tactics in Lean 4.

variable {α : Type}
variable (A B C : Set α)

-- Proof 1: Intersection is commutative
theorem inter_comm_proof : A ∩ B = B ∩ A := by
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

-- Proof 2: Subset transitivity
theorem subset_trans_proof (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x hx
  apply h2
  apply h1
  exact hx
