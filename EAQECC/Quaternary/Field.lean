import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic

/-!
四元域及论文所用的二元坐标基。通过二次不可约多项式构造四元域，
选择两个非平凡元素作为基，并定义共轭与域迹。
-/

namespace Quantum
namespace Quaternary

open Polynomial

/- 四元域的构造多项式。以下证明其首一、二次及不可约性，并据此定义四元域。
-/
noncomputable def quaternaryPolynomial : (ZMod 2)[X] :=
  X ^ 2 + X + 1

theorem quaternaryPolynomial_monic : quaternaryPolynomial.Monic := by
  rw [quaternaryPolynomial]
  monicity
  norm_num

theorem quaternaryPolynomial_natDegree :
    quaternaryPolynomial.natDegree = 2 := by
  rw [quaternaryPolynomial]
  compute_degree
  norm_num

theorem quaternaryPolynomial_irreducible :
    Irreducible quaternaryPolynomial := by
  by_contra h
  obtain ⟨c₁, c₂, hmul, hadd⟩ :=
    (quaternaryPolynomial_monic.not_irreducible_iff_exists_add_mul_eq_coeff
      quaternaryPolynomial_natDegree).mp h
  have hmul' : (1 : ZMod 2) = c₁ * c₂ := by
    simpa only [quaternaryPolynomial, coeff_add, coeff_X_pow, coeff_X,
      coeff_one, if_false, if_true, zero_add, add_zero] using hmul
  have hadd' : (1 : ZMod 2) = c₁ + c₂ := by
    simpa only [quaternaryPolynomial, coeff_add, coeff_X_pow, coeff_X,
      coeff_one, if_false, if_true, zero_add, add_zero] using hadd
  fin_cases c₁ <;> fin_cases c₂
  · exact one_ne_zero hmul'
  · exact one_ne_zero hmul'
  · exact one_ne_zero hmul'
  · have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    exact one_ne_zero (hadd'.trans htwo)

noncomputable instance quaternaryPolynomial_irreducibleFact :
    Fact (Irreducible quaternaryPolynomial) :=
  ⟨quaternaryPolynomial_irreducible⟩

abbrev QuaternaryField := AdjoinRoot quaternaryPolynomial

noncomputable instance quaternaryField_moduleFinite :
    Module.Finite (ZMod 2) QuaternaryField :=
  quaternaryPolynomial_monic.finite_adjoinRoot

noncomputable instance quaternaryField_finite : Finite QuaternaryField :=
  Module.finite_of_finite (ZMod 2)

instance quaternaryField_charTwo : CharP QuaternaryField 2 :=
  charP_of_injective_algebraMap' (ZMod 2) 2

/- 四元域中两个非平凡元素及自然基。以下建立它们的代数关系。
-/
noncomputable def omega : QuaternaryField :=
  AdjoinRoot.root quaternaryPolynomial

noncomputable def varpi : QuaternaryField :=
  omega ^ 2

noncomputable def naturalPowerBasis :
    PowerBasis (ZMod 2) QuaternaryField :=
  AdjoinRoot.powerBasis' quaternaryPolynomial_monic

noncomputable def naturalBasis :
    Module.Basis (Fin 2) (ZMod 2) QuaternaryField :=
  naturalPowerBasis.basis.reindex
    (finCongr quaternaryPolynomial_natDegree)

@[simp]
theorem naturalBasis_zero : naturalBasis 0 = 1 := by
  unfold naturalBasis naturalPowerBasis
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

@[simp]
theorem naturalBasis_one : naturalBasis 1 = omega := by
  unfold naturalBasis naturalPowerBasis omega
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change AdjoinRoot.root quaternaryPolynomial ^ 1 =
    AdjoinRoot.root quaternaryPolynomial
  simp

theorem omega_root_relation : omega ^ 2 + omega + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root quaternaryPolynomial
  simpa [quaternaryPolynomial, omega] using h

@[simp]
theorem omega_sq : omega ^ 2 = 1 + omega := by
  have hzero : omega ^ 2 + (omega + 1) = 0 := by
    simpa [add_assoc] using omega_root_relation
  calc
    omega ^ 2 = -(omega + 1) := eq_neg_of_add_eq_zero_left hzero
    _ = omega + 1 := CharTwo.neg_eq _
    _ = 1 + omega := add_comm _ _

theorem varpi_eq_one_add_omega : varpi = 1 + omega := by
  rw [varpi, omega_sq]

/- 从自然基变换到论文所用的二元基。以下证明坐标转换互逆、两个基元素线性无关及展开唯一。
-/
def naturalToPaperCoordinates :
    (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun v := ![v 0 + v 1, v 0]
  invFun v := ![v 1, v 0 + v 1]
  left_inv v := by
    funext i
    fin_cases i
    · rfl
    · simpa [add_comm] using CharTwo.add_cancel_right (v 1) (v 0)
  right_inv v := by
    funext i
    fin_cases i
    · simpa [add_comm] using CharTwo.add_cancel_left (v 1) (v 0)
    · rfl
  map_add' v w := by
    funext i
    fin_cases i <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' a v := by
    funext i
    fin_cases i <;> simp [mul_add]

noncomputable def paperCoordinateEquiv :
    QuaternaryField ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  naturalBasis.equivFun.trans naturalToPaperCoordinates

noncomputable def paperBasis :
    Module.Basis (Fin 2) (ZMod 2) QuaternaryField :=
  Module.Basis.ofEquivFun paperCoordinateEquiv

@[simp]
theorem paperBasis_zero : paperBasis 0 = omega := by
  apply paperBasis.equivFun.injective
  funext i
  fin_cases i <;>
    simp [paperBasis, paperCoordinateEquiv, naturalToPaperCoordinates,
      ← naturalBasis_one]

@[simp]
theorem paperBasis_one : paperBasis 1 = varpi := by
  apply paperBasis.equivFun.injective
  funext i
  fin_cases i <;>
    simp [paperBasis, paperCoordinateEquiv, naturalToPaperCoordinates,
      varpi_eq_one_add_omega, ← naturalBasis_zero, ← naturalBasis_one]

theorem omega_ne_zero : omega ≠ 0 := by
  rw [← paperBasis_zero]
  exact paperBasis.ne_zero 0

theorem varpi_ne_zero : varpi ≠ 0 := by
  rw [← paperBasis_one]
  exact paperBasis.ne_zero 1

theorem omega_ne_varpi : omega ≠ varpi := by
  intro h
  rw [← paperBasis_zero, ← paperBasis_one] at h
  have hindex : (0 : Fin 2) = 1 := paperBasis.injective h
  exact Fin.zero_ne_one hindex

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  rw [← naturalBasis_one, ← naturalBasis_zero] at h
  have hindex : (1 : Fin 2) = 0 := naturalBasis.injective h
  exact Fin.zero_ne_one hindex.symm

@[simp]
theorem paperCoordinateEquiv_eq_paperBasis_equivFun :
    paperCoordinateEquiv = paperBasis.equivFun := by
  rw [paperBasis, Module.Basis.equivFun_ofEquivFun]

@[simp]
theorem paperCoordinateEquiv_apply_combination (x z : ZMod 2) :
    paperCoordinateEquiv (x • omega + z • varpi) = ![x, z] := by
  have hcoordinates :
      paperBasis.equivFun
          (x • paperBasis 0 + z • paperBasis 1) = ![x, z] := by
    funext i
    fin_cases i <;>
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
        Module.Basis.equivFun_self, smul_eq_mul] <;>
      simp
  simpa only [paperCoordinateEquiv_eq_paperBasis_equivFun,
    paperBasis_zero, paperBasis_one] using hcoordinates

@[simp]
theorem paperCoordinateEquiv_symm_apply (x z : ZMod 2) :
    paperCoordinateEquiv.symm ![x, z] = x • omega + z • varpi := by
  apply paperCoordinateEquiv.injective
  rw [paperCoordinateEquiv.apply_symm_apply,
    paperCoordinateEquiv_apply_combination]

theorem eq_paper_combination (a : QuaternaryField) :
    a = (paperCoordinateEquiv a 0) • omega +
      (paperCoordinateEquiv a 1) • varpi := by
  symm
  calc
    _ = paperCoordinateEquiv.symm
        ![paperCoordinateEquiv a 0, paperCoordinateEquiv a 1] :=
      (paperCoordinateEquiv_symm_apply _ _).symm
    _ = paperCoordinateEquiv.symm (paperCoordinateEquiv a) := by
      congr 1
    _ = a := paperCoordinateEquiv.symm_apply_apply a

/- 四元域在二元域上的维数与元素数，以及非平凡元素之间的乘法关系。
-/
@[simp]
theorem finrank_quaternaryField :
    Module.finrank (ZMod 2) QuaternaryField = 2 := by
  simpa using Module.finrank_eq_card_basis paperBasis

@[simp]
theorem natCard_quaternaryField : Nat.card QuaternaryField = 4 := by
  calc
    Nat.card QuaternaryField = Nat.card (Fin 2 → ZMod 2) :=
      Nat.card_congr paperCoordinateEquiv.toEquiv
    _ = Nat.card (ZMod 2) ^ Nat.card (Fin 2) := Nat.card_fun
    _ = 4 := by simp

@[simp]
theorem omega_cubed : omega ^ 3 = 1 := by
  calc
    omega ^ 3 = omega * omega ^ 2 := by ring
    _ = omega * (1 + omega) := by rw [omega_sq]
    _ = omega + omega ^ 2 := by
      simp only [mul_add, mul_one, pow_two]
    _ = omega + (1 + omega) := by rw [omega_sq]
    _ = 1 := by
      simpa [add_comm] using CharTwo.add_cancel_left omega 1

@[simp]
theorem omega_mul_omega : omega * omega = varpi := by
  rw [varpi, pow_two]

@[simp]
theorem omega_mul_varpi : omega * varpi = 1 := by
  rw [varpi]
  calc
    omega * omega ^ 2 = omega ^ 3 := by ring
    _ = 1 := omega_cubed

@[simp]
theorem varpi_mul_omega : varpi * omega = 1 := by
  rw [mul_comm, omega_mul_varpi]

/-- 四元域共轭。将元素映射到其平方，交换两个非平凡基元素；连续取两次共轭恢复原元素。
-/
noncomputable def conjugation :
    QuaternaryField →ₐ[ZMod 2] QuaternaryField :=
  FiniteField.frobeniusAlgHom (ZMod 2) QuaternaryField

@[simp]
theorem conjugation_apply (x : QuaternaryField) :
    conjugation x = x ^ 2 := by
  change x ^ Fintype.card (ZMod 2) = x ^ 2
  rw [ZMod.card]

@[simp high]
theorem conjugation_omega : conjugation omega = varpi := by
  rw [conjugation_apply, varpi]

@[simp high]
theorem conjugation_varpi : conjugation varpi = omega := by
  rw [conjugation_apply, varpi]
  calc
    (omega ^ 2) ^ 2 = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_cubed, one_mul]

@[simp]
theorem varpi_sq : varpi ^ 2 = omega := by
  simpa only [conjugation_apply] using conjugation_varpi

@[simp]
theorem varpi_mul_varpi : varpi * varpi = omega := by
  rw [← pow_two, varpi_sq]

@[simp]
theorem conjugation_involutive (x : QuaternaryField) :
    conjugation (conjugation x) = x := by
  rw [conjugation_apply, conjugation_apply]
  letI := Fintype.ofFinite QuaternaryField
  have hcard : Fintype.card QuaternaryField = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_quaternaryField
  have hpow := FiniteField.pow_card x
  rw [hcard] at hpow
  calc
    (x ^ 2) ^ 2 = x ^ 4 := by ring
    _ = x := hpow

@[simp]
theorem conjugation_paper_combination (x z : ZMod 2) :
    conjugation (x • omega + z • varpi) =
      x • varpi + z • omega := by
  rw [map_add, map_smul, map_smul, conjugation_omega,
    conjugation_varpi]

/-- 四元域到二元域的域迹。将四元元素及其共轭之和写成二元域元素，
后续计算四个域元素的迹及论文坐标下的迹公式。
-/
noncomputable def fieldTrace :
    QuaternaryField →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) QuaternaryField

theorem algebraMap_fieldTrace (x : QuaternaryField) :
    algebraMap (ZMod 2) QuaternaryField (fieldTrace x) = x + x ^ 2 := by
  have h :=
    FiniteField.algebraMap_trace_eq_sum_pow
      (ZMod 2) QuaternaryField x
  rw [finrank_quaternaryField, Nat.card_zmod] at h
  simpa [fieldTrace, Finset.sum_range_succ] using h

@[simp]
theorem fieldTrace_zero : fieldTrace 0 = 0 := by
  exact map_zero fieldTrace

@[simp]
theorem fieldTrace_one : fieldTrace 1 = 0 := by
  apply (algebraMap (ZMod 2) QuaternaryField).injective
  rw [algebraMap_fieldTrace]
  simp [CharTwo.add_self_eq_zero]

@[simp]
theorem fieldTrace_omega : fieldTrace omega = 1 := by
  apply (algebraMap (ZMod 2) QuaternaryField).injective
  rw [algebraMap_fieldTrace, map_one, omega_sq]
  simpa [add_comm] using CharTwo.add_cancel_left omega 1

@[simp]
theorem fieldTrace_varpi : fieldTrace varpi = 1 := by
  apply (algebraMap (ZMod 2) QuaternaryField).injective
  rw [algebraMap_fieldTrace, map_one, varpi_sq,
    varpi_eq_one_add_omega]
  exact CharTwo.add_cancel_right 1 omega

@[simp]
theorem fieldTrace_paper_combination (x z : ZMod 2) :
    fieldTrace (x • omega + z • varpi) = x + z := by
  rw [map_add, map_smul, map_smul, fieldTrace_omega,
    fieldTrace_varpi]
  simp

end Quaternary
end Quantum
