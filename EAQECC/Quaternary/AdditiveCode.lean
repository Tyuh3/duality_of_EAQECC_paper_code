import EAQECC.Quaternary.Field
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
四元加性码、迹内积与汉明重量。加性码按二元域上的子空间建模，
迹内积用于定义迹对偶、迹根空间和限制迹形式的秩。
-/

namespace Quantum
namespace Quaternary

/- 长度为 n 的四元向量，以及由这些向量组成的二元线性子空间，即四元加性码。
-/
abbrev QuaternaryVector (n : ℕ) := Fin n → QuaternaryField

abbrev QuaternaryAdditiveCode (n : ℕ) :=
  Submodule (ZMod 2) (QuaternaryVector n)

/-- 迹内积。将各坐标的元素与另一向量共轭坐标的乘积求迹后相加，结果位于二元域。
以下证明它在二元域上双线性、对称且交替。
-/
noncomputable def traceInner {n : ℕ}
    (u v : QuaternaryVector n) : ZMod 2 :=
  ∑ i, fieldTrace (u i * conjugation (v i))

theorem fieldTrace_mul_conjugation_paper
    (x z x' z' : ZMod 2) :
    fieldTrace
        ((x • omega + z • varpi) *
          conjugation (x' • omega + z' • varpi)) =
      x * z' + z * x' := by
  rw [conjugation_paper_combination, mul_add, add_mul, add_mul]
  simp only [map_add, smul_mul_smul, map_smul,
    omega_mul_varpi, varpi_mul_omega,
    omega_mul_omega, varpi_mul_varpi,
    fieldTrace_one, fieldTrace_omega, fieldTrace_varpi]
  simp [add_comm]

theorem fieldTrace_mul_conjugation_eq_coordinates
    (a b : QuaternaryField) :
    fieldTrace (a * conjugation b) =
      paperCoordinateEquiv a 0 * paperCoordinateEquiv b 1 +
        paperCoordinateEquiv a 1 * paperCoordinateEquiv b 0 := by
  calc
    fieldTrace (a * conjugation b) =
        fieldTrace
          (((paperCoordinateEquiv a 0) • omega +
              (paperCoordinateEquiv a 1) • varpi) *
            conjugation
              ((paperCoordinateEquiv b 0) • omega +
                (paperCoordinateEquiv b 1) • varpi)) := by
      rw [← eq_paper_combination a, ← eq_paper_combination b]
    _ = _ := fieldTrace_mul_conjugation_paper _ _ _ _

theorem traceInner_add_left {n : ℕ}
    (u v w : QuaternaryVector n) :
    traceInner (u + v) w = traceInner u w + traceInner v w := by
  simp [traceInner, add_mul, Finset.sum_add_distrib]

theorem traceInner_smul_left {n : ℕ}
    (a : ZMod 2) (u v : QuaternaryVector n) :
    traceInner (a • u) v = a * traceInner u v := by
  simp [traceInner, Finset.mul_sum]

theorem traceInner_add_right {n : ℕ}
    (u v w : QuaternaryVector n) :
    traceInner u (v + w) = traceInner u v + traceInner u w := by
  simp only [traceInner, Pi.add_apply, map_add, mul_add,
    Finset.sum_add_distrib]

theorem traceInner_smul_right {n : ℕ}
    (a : ZMod 2) (u v : QuaternaryVector n) :
    traceInner u (a • v) = a * traceInner u v := by
  simp [traceInner, Finset.mul_sum]

noncomputable def traceBilinForm (n : ℕ) :
    LinearMap.BilinForm (ZMod 2) (QuaternaryVector n) :=
  LinearMap.mk₂ (ZMod 2)
    traceInner
    traceInner_add_left
    (by
      intro a u v
      simpa [smul_eq_mul] using traceInner_smul_left a u v)
    traceInner_add_right
    (by
      intro a u v
      simpa [smul_eq_mul] using traceInner_smul_right a u v)

@[simp]
theorem traceBilinForm_apply {n : ℕ} (u v : QuaternaryVector n) :
    traceBilinForm n u v = traceInner u v := by
  rfl

theorem traceInner_symm {n : ℕ} (u v : QuaternaryVector n) :
    traceInner u v = traceInner v u := by
  unfold traceInner
  apply Finset.sum_congr rfl
  intro i _
  rw [fieldTrace_mul_conjugation_eq_coordinates,
    fieldTrace_mul_conjugation_eq_coordinates]
  ring

theorem traceInner_self {n : ℕ} (u : QuaternaryVector n) :
    traceInner u u = 0 := by
  unfold traceInner
  apply Finset.sum_eq_zero
  intro i _
  rw [fieldTrace_mul_conjugation_eq_coordinates]
  simpa [mul_comm] using
    CharTwo.add_self_eq_zero
      (paperCoordinateEquiv (u i) 0 * paperCoordinateEquiv (u i) 1)

theorem traceBilinForm_isSymm (n : ℕ) :
    (traceBilinForm n).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  exact traceInner_symm

theorem traceBilinForm_isAlt (n : ℕ) :
    (traceBilinForm n).IsAlt := by
  exact traceInner_self

/-- 迹对偶。由与 C 中每个向量的迹内积均为零的四元向量组成。
后续将这一条件与双线性形式的正交补对应。
-/
noncomputable def traceOrthogonal {n : ℕ}
    (C : QuaternaryAdditiveCode n) : QuaternaryAdditiveCode n where
  carrier := {u | ∀ v ∈ C, traceInner u v = 0}
  zero_mem' := by
    intro v _
    simp [traceInner]
  add_mem' := by
    intro u v hu hv w hw
    rw [traceInner_add_left, hu w hw, hv w hw, zero_add]
  smul_mem' := by
    intro a u hu v hv
    rw [traceInner_smul_left, hu v hv, mul_zero]

@[simp]
theorem mem_traceOrthogonal_iff {n : ℕ}
    (C : QuaternaryAdditiveCode n) (u : QuaternaryVector n) :
    u ∈ traceOrthogonal C ↔ ∀ v ∈ C, traceInner u v = 0 := by
  rfl

theorem traceOrthogonal_eq_bilinForm_orthogonal {n : ℕ}
    (C : QuaternaryAdditiveCode n) :
    traceOrthogonal C = (traceBilinForm n).orthogonal C := by
  ext u
  constructor
  · intro hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    change traceInner v u = 0
    rw [traceInner_symm]
    exact hu v hv
  · intro hu v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu
    rw [traceInner_symm]
    exact hu v hv

/-- 迹根空间。由同时属于 C 及其迹对偶的向量组成，即 R(C) = C ∩ C⊥。
它记录限制在 C 上的迹形式的退化方向。
-/
noncomputable def traceRadical {n : ℕ}
    (C : QuaternaryAdditiveCode n) : QuaternaryAdditiveCode n :=
  C ⊓ traceOrthogonal C

@[simp]
theorem mem_traceRadical_iff {n : ℕ}
    (C : QuaternaryAdditiveCode n) (u : QuaternaryVector n) :
    u ∈ traceRadical C ↔ u ∈ C ∧ u ∈ traceOrthogonal C := by
  rfl

theorem traceRadical_le_traceOrthogonal_traceRadical {n : ℕ}
    (C : QuaternaryAdditiveCode n) :
    traceRadical C ≤ traceOrthogonal (traceRadical C) := by
  intro u hu v hv
  exact hu.2 v hv.1

namespace QuaternaryAdditiveCode

/- 限制迹形式的秩，随后定义汉明支集、汉明重量及重量枚举多项式。
重量按非零四元坐标的个数计算。
-/
noncomputable def traceRank {n : ℕ}
    (C : QuaternaryAdditiveCode n) : ℕ :=
  Module.finrank (ZMod 2)
    (LinearMap.range ((traceBilinForm n).restrict C))

end QuaternaryAdditiveCode

noncomputable def hammingSupport {n : ℕ}
    (u : QuaternaryVector n) : Finset (Fin n) :=
  Finset.univ.filter fun i => u i ≠ 0

noncomputable def hammingWeight {n : ℕ} (u : QuaternaryVector n) : ℕ :=
  (hammingSupport u).card

@[simp]
theorem mem_hammingSupport_iff {n : ℕ}
    (u : QuaternaryVector n) (i : Fin n) :
    i ∈ hammingSupport u ↔ u i ≠ 0 := by
  simp [hammingSupport]

theorem hammingWeight_eq_zero_iff {n : ℕ}
    (u : QuaternaryVector n) :
    hammingWeight u = 0 ↔ u = 0 := by
  constructor
  · intro hWeight
    have hSupport : hammingSupport u = ∅ :=
      Finset.card_eq_zero.mp hWeight
    funext i
    by_contra hi
    have hiSupport : i ∈ hammingSupport u :=
      (mem_hammingSupport_iff u i).mpr hi
    rw [hSupport] at hiSupport
    exact Finset.notMem_empty i hiSupport
  · rintro rfl
    simp [hammingWeight, hammingSupport]

theorem hammingWeight_pos_iff {n : ℕ}
    (u : QuaternaryVector n) :
    0 < hammingWeight u ↔ u ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq,
    hammingWeight_eq_zero_iff]

namespace QuaternaryAdditiveCode

noncomputable def hammingWeightEnumerator {n : ℕ}
    (C : QuaternaryAdditiveCode n) : Polynomial ℕ := by
  classical
  letI := Fintype.ofFinite C
  exact ∑ u : C, Polynomial.X ^ hammingWeight (u : QuaternaryVector n)

end QuaternaryAdditiveCode

end Quaternary
end Quantum
