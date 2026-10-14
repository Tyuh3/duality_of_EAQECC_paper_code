import EAQECC.Quaternary.AdditiveCode
import EAQECC.Symplectic.Distance

/-!
二元辛向量与四元向量的对应。使用论文中的四元域基，
证明坐标映射互逆，并保持辛内积与迹内积以及辛重量与汉明重量。
-/

namespace Quantum
namespace Quaternary

/-- 二元到四元的坐标映射。把每个量子比特的 X、Z 二元坐标写成四元域两个基元素的线性组合。
紧接着给出反向映射，并证明两者互逆。
-/
noncomputable def binaryToQuaternary (n : ℕ) :
    BinarySymplecticVector n ≃ₗ[ZMod 2] QuaternaryVector n where
  toFun v i :=
    v (Fin.castAdd n i) • omega + v (Fin.natAdd n i) • varpi
  invFun u :=
    Fin.addCases
      (fun i => paperCoordinateEquiv (u i) 0)
      (fun i => paperCoordinateEquiv (u i) 1)
  left_inv v := by
    funext j
    change Fin.addCases
        (fun i => paperCoordinateEquiv
          (v (Fin.castAdd n i) • omega +
            v (Fin.natAdd n i) • varpi) 0)
        (fun i => paperCoordinateEquiv
          (v (Fin.castAdd n i) • omega +
            v (Fin.natAdd n i) • varpi) 1) j = v j
    rw [show (fun i => paperCoordinateEquiv
          (v (Fin.castAdd n i) • omega +
            v (Fin.natAdd n i) • varpi) 0) =
        (fun i => v (Fin.castAdd n i)) by
          funext i
          have h := congrFun
            (paperCoordinateEquiv_apply_combination
              (v (Fin.castAdd n i)) (v (Fin.natAdd n i))) 0
          simpa using h,
      show (fun i => paperCoordinateEquiv
          (v (Fin.castAdd n i) • omega +
            v (Fin.natAdd n i) • varpi) 1) =
        (fun i => v (Fin.natAdd n i)) by
          funext i
          have h := congrFun
            (paperCoordinateEquiv_apply_combination
              (v (Fin.castAdd n i)) (v (Fin.natAdd n i))) 1
          simpa using h]
    exact congrFun (Fin.addCases_castAdd_natAdd v) j
  right_inv u := by
    funext i
    change
      @Fin.addCases n n (fun _ => ZMod 2)
          (fun i => paperCoordinateEquiv (u i) 0)
          (fun i => paperCoordinateEquiv (u i) 1)
          (Fin.castAdd n i) • omega +
        @Fin.addCases n n (fun _ => ZMod 2)
          (fun i => paperCoordinateEquiv (u i) 0)
          (fun i => paperCoordinateEquiv (u i) 1)
          (Fin.natAdd n i) • varpi = u i
    rw [Fin.addCases_left, Fin.addCases_right]
    exact (eq_paper_combination (u i)).symm
  map_add' v w := by
    funext i
    simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' a v := by
    funext i
    simp [smul_smul]

noncomputable def quaternaryToBinary (n : ℕ) :
    QuaternaryVector n ≃ₗ[ZMod 2] BinarySymplecticVector n :=
  (binaryToQuaternary n).symm

@[simp]
theorem binaryToQuaternary_apply {n : ℕ}
    (v : BinarySymplecticVector n) (i : Fin n) :
    binaryToQuaternary n v i =
      v (Fin.castAdd n i) • omega + v (Fin.natAdd n i) • varpi := by
  rfl

@[simp]
theorem quaternaryToBinary_apply_castAdd {n : ℕ}
    (u : QuaternaryVector n) (i : Fin n) :
    quaternaryToBinary n u (Fin.castAdd n i) =
      paperCoordinateEquiv (u i) 0 := by
  change Fin.addCases
      (fun i => paperCoordinateEquiv (u i) 0)
      (fun i => paperCoordinateEquiv (u i) 1)
      (Fin.castAdd n i) = paperCoordinateEquiv (u i) 0
  exact Fin.addCases_left _

@[simp]
theorem quaternaryToBinary_apply_natAdd {n : ℕ}
    (u : QuaternaryVector n) (i : Fin n) :
    quaternaryToBinary n u (Fin.natAdd n i) =
      paperCoordinateEquiv (u i) 1 := by
  change Fin.addCases
      (fun i => paperCoordinateEquiv (u i) 0)
      (fun i => paperCoordinateEquiv (u i) 1)
      (Fin.natAdd n i) = paperCoordinateEquiv (u i) 1
  exact Fin.addCases_right _

@[simp]
theorem binaryToQuaternary_quaternaryToBinary {n : ℕ}
    (u : QuaternaryVector n) :
    binaryToQuaternary n (quaternaryToBinary n u) = u :=
  (binaryToQuaternary n).apply_symm_apply u

@[simp]
theorem quaternaryToBinary_binaryToQuaternary {n : ℕ}
    (v : BinarySymplecticVector n) :
    quaternaryToBinary n (binaryToQuaternary n v) = v :=
  (binaryToQuaternary n).symm_apply_apply v

/- 坐标映射把二元辛内积转化为四元迹内积。以下同时给出反向转换的对应关系。
-/
theorem traceInner_binaryToQuaternary {n : ℕ}
    (v w : BinarySymplecticVector n) :
    traceInner (binaryToQuaternary n v) (binaryToQuaternary n w) =
      NQubitPauliOperator.symplecticBilinear v w := by
  unfold traceInner NQubitPauliOperator.symplecticBilinear
  apply Finset.sum_congr rfl
  intro i _
  exact fieldTrace_mul_conjugation_paper _ _ _ _

theorem traceBilinForm_binaryToQuaternary {n : ℕ}
    (v w : BinarySymplecticVector n) :
    traceBilinForm n (binaryToQuaternary n v)
        (binaryToQuaternary n w) =
      binarySymplecticBilinForm n v w := by
  exact traceInner_binaryToQuaternary v w

theorem symplecticBilinear_quaternaryToBinary {n : ℕ}
    (u v : QuaternaryVector n) :
    NQubitPauliOperator.symplecticBilinear
        (quaternaryToBinary n u) (quaternaryToBinary n v) =
      traceInner u v := by
  rw [← traceInner_binaryToQuaternary
    (quaternaryToBinary n u) (quaternaryToBinary n v)]
  simp

theorem binarySymplecticBilinForm_quaternaryToBinary {n : ℕ}
    (u v : QuaternaryVector n) :
    binarySymplecticBilinForm n
        (quaternaryToBinary n u) (quaternaryToBinary n v) =
      traceBilinForm n u v := by
  exact symplecticBilinear_quaternaryToBinary u v

/- 一个四元坐标为零，当且仅当对应的两个二元坐标均为零。
以下由此证明支集与重量在转换下保持。
-/
theorem paper_combination_eq_zero_iff (x z : ZMod 2) :
    x • omega + z • varpi = 0 ↔ x = 0 ∧ z = 0 := by
  constructor
  · intro h
    have hCoordinates : ![x, z] = (0 : Fin 2 → ZMod 2) := by
      calc
        ![x, z] = paperCoordinateEquiv (x • omega + z • varpi) :=
          (paperCoordinateEquiv_apply_combination x z).symm
        _ = paperCoordinateEquiv 0 := congrArg paperCoordinateEquiv h
        _ = 0 := map_zero paperCoordinateEquiv
    have hx := congrFun hCoordinates 0
    have hz := congrFun hCoordinates 1
    exact ⟨by simpa using hx, by simpa using hz⟩
  · rintro ⟨rfl, rfl⟩
    simp

theorem paper_combination_ne_zero_iff (x z : ZMod 2) :
    x • omega + z • varpi ≠ 0 ↔ x ≠ 0 ∨ z ≠ 0 := by
  rw [ne_eq, paper_combination_eq_zero_iff, not_and_or]

theorem hammingSupport_binaryToQuaternary {n : ℕ}
    (v : BinarySymplecticVector n) :
    hammingSupport (binaryToQuaternary n v) = symplecticSupport v := by
  ext i
  rw [mem_hammingSupport_iff, mem_symplecticSupport_iff,
    binaryToQuaternary_apply, paper_combination_ne_zero_iff]

@[simp]
theorem hammingWeight_binaryToQuaternary {n : ℕ}
    (v : BinarySymplecticVector n) :
    hammingWeight (binaryToQuaternary n v) = symplecticWeight v := by
  rw [hammingWeight, symplecticWeight,
    hammingSupport_binaryToQuaternary]

theorem symplecticSupport_quaternaryToBinary {n : ℕ}
    (u : QuaternaryVector n) :
    symplecticSupport (quaternaryToBinary n u) = hammingSupport u := by
  rw [← hammingSupport_binaryToQuaternary (quaternaryToBinary n u)]
  simp

@[simp]
theorem symplecticWeight_quaternaryToBinary {n : ℕ}
    (u : QuaternaryVector n) :
    symplecticWeight (quaternaryToBinary n u) = hammingWeight u := by
  rw [symplecticWeight, hammingWeight,
    symplecticSupport_quaternaryToBinary]

end Quaternary
end Quantum
