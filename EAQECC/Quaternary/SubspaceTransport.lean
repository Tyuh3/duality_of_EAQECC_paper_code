import EAQECC.Quaternary.SymplecticBridge

/-!
二元辛子空间与四元加性码的对应。将坐标映射推广到子空间，
证明维数、类型、对偶及根空间的对应，并提供迹内积矩阵的类型判定。
-/

namespace Quantum
namespace Quaternary

/- 二元与四元子空间的互逆转换。以下证明成员判定、互逆关系及二元维数保持。
-/
noncomputable def binaryToQuaternarySubspace {n : ℕ}
    (S : BinarySymplecticSubspace n) : QuaternaryAdditiveCode n :=
  S.map (binaryToQuaternary n).toLinearMap

noncomputable def quaternaryToBinarySubspace {n : ℕ}
    (C : QuaternaryAdditiveCode n) : BinarySymplecticSubspace n :=
  C.map (quaternaryToBinary n).toLinearMap

noncomputable def binaryToQuaternarySubspaceEquiv {n : ℕ}
    (S : BinarySymplecticSubspace n) :
    S ≃ₗ[ZMod 2] binaryToQuaternarySubspace S :=
  (binaryToQuaternary n).submoduleMap S

@[simp]
theorem mem_binaryToQuaternarySubspace_iff {n : ℕ}
    (S : BinarySymplecticSubspace n) (u : QuaternaryVector n) :
    u ∈ binaryToQuaternarySubspace S ↔
      quaternaryToBinary n u ∈ S := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro hu
    exact ⟨quaternaryToBinary n u, hu, by simp⟩

@[simp]
theorem mem_quaternaryToBinarySubspace_iff {n : ℕ}
    (C : QuaternaryAdditiveCode n) (v : BinarySymplecticVector n) :
    v ∈ quaternaryToBinarySubspace C ↔
      binaryToQuaternary n v ∈ C := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro hv
    exact ⟨binaryToQuaternary n v, hv, by simp⟩

@[simp]
theorem quaternaryToBinarySubspace_binaryToQuaternarySubspace
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    quaternaryToBinarySubspace (binaryToQuaternarySubspace S) = S := by
  ext v
  simp

@[simp]
theorem binaryToQuaternarySubspace_quaternaryToBinarySubspace
    {n : ℕ} (C : QuaternaryAdditiveCode n) :
    binaryToQuaternarySubspace (quaternaryToBinarySubspace C) = C := by
  ext u
  simp

@[simp]
theorem finrank_binaryToQuaternarySubspace {n : ℕ}
    (S : BinarySymplecticSubspace n) :
    Module.finrank (ZMod 2) (binaryToQuaternarySubspace S) =
      Module.finrank (ZMod 2) S := by
  exact (binaryToQuaternary n).finrank_map_eq S

@[simp]
theorem finrank_quaternaryToBinarySubspace {n : ℕ}
    (C : QuaternaryAdditiveCode n) :
    Module.finrank (ZMod 2) (quaternaryToBinarySubspace C) =
      Module.finrank (ZMod 2) C := by
  exact (quaternaryToBinary n).finrank_map_eq C

namespace QuaternaryAdditiveCode

/-- 迹类型 [m,c]ₜ。通过对应二元辛子空间的辛类型定义四元加性码的类型。
后续证明它等价于加性码的二元维数为 m、限制迹形式的秩为 2c。
-/
def HasTraceType {n : ℕ}
    (C : QuaternaryAdditiveCode n) (m c : ℕ) : Prop :=
  ∃ S : BinarySymplecticSubspace n,
    S.HasType m c ∧ C = binaryToQuaternarySubspace S

theorem hasTraceType_binaryToQuaternarySubspace
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (hType : S.HasType m c) :
    (binaryToQuaternarySubspace S).HasTraceType m c := by
  exact ⟨S, hType, rfl⟩

theorem hasTraceType_iff_preimage_hasType
    {n m c : ℕ} {C : QuaternaryAdditiveCode n} :
    C.HasTraceType m c ↔
      (quaternaryToBinarySubspace C).HasType m c := by
  constructor
  · rintro ⟨S, hType, rfl⟩
    simpa using hType
  · intro hType
    exact ⟨quaternaryToBinarySubspace C, hType,
      (binaryToQuaternarySubspace_quaternaryToBinarySubspace C).symm⟩

theorem finrank_eq_of_hasTraceType
    {n m c : ℕ} {C : QuaternaryAdditiveCode n}
    (hType : C.HasTraceType m c) :
    Module.finrank (ZMod 2) C = m := by
  have hPreimage :=
    hasTraceType_iff_preimage_hasType.mp hType
  rw [← finrank_quaternaryToBinarySubspace C]
  exact hPreimage.1

end QuaternaryAdditiveCode

/- 双线性形式的秩与其基矩阵的秩一致，为迹类型的矩阵判定提供依据。
-/
private theorem finrank_range_bilinForm_eq_rank_toMatrix
    {V ι : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm (ZMod 2) V) (hSymm : B.IsSymm)
    (b : Module.Basis ι (ZMod 2) V) :
    Module.finrank (ZMod 2) (LinearMap.range B) =
      Matrix.rank (LinearMap.BilinForm.toMatrix b B) := by
  let M : Matrix ι ι (ZMod 2) :=
    LinearMap.toMatrix b b.dualBasis B
  have hMatrix : M = LinearMap.BilinForm.toMatrix b B := by
    ext i j
    simp only [M, LinearMap.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply,
      Module.Basis.dualBasis_repr]
    exact hSymm.eq (b j) (b i)
  have hMatrixRank :=
    Matrix.rank_eq_finrank_range_toLin M b.dualBasis b
  rw [Matrix.toLin_toMatrix] at hMatrixRank
  rw [← hMatrixRank, hMatrix]

/- 四元矩阵的二元行张成空间、迹内积矩阵和共轭转置。
以下在线性无关的行基条件下，将限制迹形式的秩转化为迹内积矩阵秩。
-/
noncomputable def quaternaryMatrixRowSpace {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) QuaternaryField) :
    QuaternaryAdditiveCode n :=
  Submodule.span (ZMod 2) (Set.range G.row)

noncomputable def traceGramMatrix {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) QuaternaryField) :
    Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun i j => traceInner (G.row i) (G.row j)

noncomputable def quaternaryConjugateMatrix {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) QuaternaryField) :
    Matrix (Fin m) (Fin n) QuaternaryField :=
  fun i j => conjugation (G i j)

noncomputable def quaternaryConjugateTranspose {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) QuaternaryField) :
    Matrix (Fin n) (Fin m) QuaternaryField :=
  (quaternaryConjugateMatrix G).transpose

theorem algebraMap_fieldTrace_mul_conjugation
    (a b : QuaternaryField) :
    algebraMap (ZMod 2) QuaternaryField
        (fieldTrace (a * conjugation b)) =
      a * conjugation b + conjugation a * b := by
  rw [algebraMap_fieldTrace, mul_pow,
    ← conjugation_apply a,
    ← conjugation_apply (conjugation b),
    conjugation_involutive]

theorem map_traceGramMatrix_eq_mul_conjugateTranspose_add
    {m n : ℕ} (G : Matrix (Fin m) (Fin n) QuaternaryField) :
    (traceGramMatrix G).map
        (algebraMap (ZMod 2) QuaternaryField) =
      G * quaternaryConjugateTranspose G +
        quaternaryConjugateMatrix G * G.transpose := by
  ext i j
  simp only [Matrix.map_apply, traceGramMatrix, traceInner,
    map_sum, algebraMap_fieldTrace_mul_conjugation,
    Matrix.add_apply, Matrix.mul_apply,
    quaternaryConjugateTranspose, quaternaryConjugateMatrix,
    Matrix.transpose_apply, Matrix.row_apply]
  rw [Finset.sum_add_distrib]

theorem traceRank_quaternaryMatrixRowSpace
    {m n : ℕ} (G : Matrix (Fin m) (Fin n) QuaternaryField)
    (hG : LinearIndependent (ZMod 2) G.row) :
    (quaternaryMatrixRowSpace G).traceRank =
      Matrix.rank (traceGramMatrix G) := by
  classical
  let C := quaternaryMatrixRowSpace G
  let b : Module.Basis (Fin m) (ZMod 2) C := Module.Basis.span hG
  let B := (traceBilinForm n).restrict C
  have hBSymm : B.IsSymm := by
    simpa [B] using (traceBilinForm_isSymm n).restrict C
  have hGramMatrix :
      LinearMap.BilinForm.toMatrix b B = traceGramMatrix G := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply]
    change traceInner (b i).1 (b j).1 =
      traceInner (G.row i) (G.row j)
    have hi : (b i).1 = G.row i := by
      change (↑((Module.Basis.span hG) i) : QuaternaryVector n) = G.row i
      exact Module.Basis.coe_span_apply hG i
    have hj : (b j).1 = G.row j := by
      change (↑((Module.Basis.span hG) j) : QuaternaryVector n) = G.row j
      exact Module.Basis.coe_span_apply hG j
    rw [hi, hj]
  unfold QuaternaryAdditiveCode.traceRank
  rw [show (traceBilinForm n).restrict C = B from rfl,
    finrank_range_bilinForm_eq_rank_toMatrix B hBSymm b,
    hGramMatrix]

theorem traceRank_binaryToQuaternarySubspace
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    (binaryToQuaternarySubspace S).traceRank = S.symplecticRank := by
  classical
  let eS := binaryToQuaternarySubspaceEquiv S
  let bS := Module.finBasis (ZMod 2) S
  let bC := bS.map eS
  let Bs := (binarySymplecticBilinForm n).restrict S
  let Bt := (traceBilinForm n).restrict (binaryToQuaternarySubspace S)
  have hBsSymm : Bs.IsSymm := by
    simpa [Bs] using (binarySymplecticBilinForm_isSymm n).restrict S
  have hBtSymm : Bt.IsSymm := by
    simpa [Bt] using (traceBilinForm_isSymm n).restrict
      (binaryToQuaternarySubspace S)
  have hMatrices :
      LinearMap.BilinForm.toMatrix bC Bt =
        LinearMap.BilinForm.toMatrix bS Bs := by
    ext i j
    simp [bC, eS, binaryToQuaternarySubspaceEquiv, Bt, Bs]
    change traceInner
        (binaryToQuaternary n (bS i : BinarySymplecticVector n))
        (binaryToQuaternary n (bS j : BinarySymplecticVector n)) =
      NQubitPauliOperator.symplecticBilinear
        (bS i : BinarySymplecticVector n)
        (bS j : BinarySymplecticVector n)
    exact traceInner_binaryToQuaternary _ _
  unfold QuaternaryAdditiveCode.traceRank
    BinarySymplecticSubspace.symplecticRank
  rw [show (traceBilinForm n).restrict (binaryToQuaternarySubspace S) = Bt
      from rfl,
    show (binarySymplecticBilinForm n).restrict S = Bs from rfl,
    finrank_range_bilinForm_eq_rank_toMatrix Bt hBtSymm bC,
    finrank_range_bilinForm_eq_rank_toMatrix Bs hBsSymm bS,
    hMatrices]

theorem traceRank_eq_symplecticRank_preimage
    {n : ℕ} (C : QuaternaryAdditiveCode n) :
    C.traceRank = (quaternaryToBinarySubspace C).symplecticRank := by
  rw [← traceRank_binaryToQuaternarySubspace
    (quaternaryToBinarySubspace C)]
  simp

namespace QuaternaryAdditiveCode

/-- 迹类型的维数与迹秩判定。加性码具有类型 [m,c]ₜ，
当且仅当其二元维数为 m、限制迹形式的秩为 2c。
紧接着的矩阵判定将这一条件应用于二元线性无关的四元生成行。
-/
theorem hasTraceType_iff_finrank_and_traceRank
    {n m c : ℕ} {C : QuaternaryAdditiveCode n} :
    C.HasTraceType m c ↔
      Module.finrank (ZMod 2) C = m ∧ C.traceRank = 2 * c := by
  rw [hasTraceType_iff_preimage_hasType]
  unfold BinarySymplecticSubspace.HasType
  rw [finrank_quaternaryToBinarySubspace,
    traceRank_eq_symplecticRank_preimage]

end QuaternaryAdditiveCode

theorem quaternaryMatrixRowSpace_hasTraceType_iff
    {m n c : ℕ} (G : Matrix (Fin m) (Fin n) QuaternaryField)
    (hG : LinearIndependent (ZMod 2) G.row) :
    (quaternaryMatrixRowSpace G).HasTraceType m c ↔
      Matrix.rank (traceGramMatrix G) = 2 * c := by
  have hDimension :
      Module.finrank (ZMod 2) (quaternaryMatrixRowSpace G) = m := by
    let b : Module.Basis (Fin m) (ZMod 2)
        (quaternaryMatrixRowSpace G) := Module.Basis.span hG
    simpa using Module.finrank_eq_card_basis b
  rw [QuaternaryAdditiveCode.hasTraceType_iff_finrank_and_traceRank,
    hDimension, traceRank_quaternaryMatrixRowSpace G hG]
  simp

/-- 辛对偶与迹对偶的对应。先取二元辛对偶再转为四元子空间，
与先转换子空间再取迹对偶所得的结果相同。后续建立反向对应及根空间保持关系。
-/
theorem binaryToQuaternarySubspace_sympOrthogonal
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    binaryToQuaternarySubspace
        (NQubitPauliGroupElement.sympOrthogonal S) =
      traceOrthogonal (binaryToQuaternarySubspace S) := by
  ext u
  constructor
  · intro hu
    have huPreimage := (mem_binaryToQuaternarySubspace_iff _ _).mp hu
    rw [mem_traceOrthogonal_iff]
    intro v hv
    have hvPreimage := (mem_binaryToQuaternarySubspace_iff _ _).mp hv
    have hPairing := huPreimage _ hvPreimage
    rwa [symplecticBilinear_quaternaryToBinary] at hPairing
  · intro hu
    apply (mem_binaryToQuaternarySubspace_iff _ _).mpr
    rw [mem_traceOrthogonal_iff] at hu
    intro w hw
    calc
      NQubitPauliOperator.symplecticBilinear
          (quaternaryToBinary n u) w =
          traceInner u (binaryToQuaternary n w) := by
        rw [← symplecticBilinear_quaternaryToBinary
          u (binaryToQuaternary n w)]
        simp
      _ = 0 := hu _
        ((mem_binaryToQuaternarySubspace_iff S _).mpr (by simpa using hw))

theorem quaternaryToBinarySubspace_traceOrthogonal
    {n : ℕ} (C : QuaternaryAdditiveCode n) :
    quaternaryToBinarySubspace (traceOrthogonal C) =
      NQubitPauliGroupElement.sympOrthogonal
        (quaternaryToBinarySubspace C) := by
  have h := binaryToQuaternarySubspace_sympOrthogonal
    (quaternaryToBinarySubspace C)
  have hMapped := congrArg quaternaryToBinarySubspace h
  simpa using hMapped.symm

theorem binaryToQuaternarySubspace_radical
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    binaryToQuaternarySubspace (symplecticRadical S) =
      traceRadical (binaryToQuaternarySubspace S) := by
  ext u
  constructor
  · intro hu
    have huPreimage := (mem_binaryToQuaternarySubspace_iff _ _).mp hu
    refine ⟨(mem_binaryToQuaternarySubspace_iff S _).mpr huPreimage.1, ?_⟩
    rw [← binaryToQuaternarySubspace_sympOrthogonal S]
    exact (mem_binaryToQuaternarySubspace_iff _ _).mpr huPreimage.2
  · intro hu
    apply (mem_binaryToQuaternarySubspace_iff _ _).mpr
    refine ⟨(mem_binaryToQuaternarySubspace_iff S _).mp hu.1, ?_⟩
    have huOrthogonal :
        u ∈ binaryToQuaternarySubspace
          (NQubitPauliGroupElement.sympOrthogonal S) := by
      rw [binaryToQuaternarySubspace_sympOrthogonal S]
      exact hu.2
    exact (mem_binaryToQuaternarySubspace_iff _ _).mp huOrthogonal

theorem quaternaryToBinarySubspace_traceRadical
    {n : ℕ} (C : QuaternaryAdditiveCode n) :
    quaternaryToBinarySubspace (traceRadical C) =
      symplecticRadical (quaternaryToBinarySubspace C) := by
  have h := binaryToQuaternarySubspace_radical
    (quaternaryToBinarySubspace C)
  have hMapped := congrArg quaternaryToBinarySubspace h
  simpa using hMapped.symm

theorem traceRadical_traceOrthogonal
    {n : ℕ} (C : QuaternaryAdditiveCode n) :
    traceRadical (traceOrthogonal C) = traceRadical C := by
  have hBinary :
      quaternaryToBinarySubspace
          (traceRadical (traceOrthogonal C)) =
        quaternaryToBinarySubspace (traceRadical C) := by
    rw [quaternaryToBinarySubspace_traceRadical,
      quaternaryToBinarySubspace_traceRadical,
      quaternaryToBinarySubspace_traceOrthogonal]
    exact BinarySymplecticSubspace.radical_sympOrthogonal
      (quaternaryToBinarySubspace C)
  calc
    traceRadical (traceOrthogonal C) =
        binaryToQuaternarySubspace
          (quaternaryToBinarySubspace
            (traceRadical (traceOrthogonal C))) :=
      (binaryToQuaternarySubspace_quaternaryToBinarySubspace _).symm
    _ = binaryToQuaternarySubspace
          (quaternaryToBinarySubspace (traceRadical C)) :=
      congrArg (binaryToQuaternarySubspace (n := n)) hBinary
    _ = traceRadical C :=
      binaryToQuaternarySubspace_quaternaryToBinarySubspace _

@[simp]
theorem finrank_traceRadical_binaryToQuaternarySubspace
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    Module.finrank (ZMod 2)
        (traceRadical (binaryToQuaternarySubspace S)) =
      Module.finrank (ZMod 2) (symplecticRadical S) := by
  rw [← binaryToQuaternarySubspace_radical S,
    finrank_binaryToQuaternarySubspace]

namespace QuaternaryAdditiveCode

/- 由二元辛理论推出四元加性码的根空间维数关系、类型参数界和迹对偶类型。
-/
theorem radicalFinrank_add_two_mul_eq_of_hasTraceType
    {n m c : ℕ} {C : QuaternaryAdditiveCode n}
    (hType : C.HasTraceType m c) :
    Module.finrank (ZMod 2) (traceRadical C) + 2 * c = m := by
  have hPreimage :=
    hasTraceType_iff_preimage_hasType.mp hType
  have hBinary :=
    BinarySymplecticSubspace.radicalFinrank_add_two_mul_eq_of_hasType
      hPreimage
  have hRadicalFinrank :
      Module.finrank (ZMod 2) (traceRadical C) =
        Module.finrank (ZMod 2)
          (symplecticRadical (quaternaryToBinarySubspace C)) := by
    calc
      Module.finrank (ZMod 2) (traceRadical C) =
          Module.finrank (ZMod 2)
            (quaternaryToBinarySubspace (traceRadical C)) :=
        (finrank_quaternaryToBinarySubspace (traceRadical C)).symm
      _ = Module.finrank (ZMod 2)
          (symplecticRadical (quaternaryToBinarySubspace C)) := by
        rw [quaternaryToBinarySubspace_traceRadical C]
  rw [hRadicalFinrank]
  exact hBinary

theorem two_mul_typeParameter_le_of_hasTraceType
    {n m c : ℕ} {C : QuaternaryAdditiveCode n}
    (hType : C.HasTraceType m c) :
    2 * c ≤ m := by
  have hRadical :=
    radicalFinrank_add_two_mul_eq_of_hasTraceType hType
  omega

theorem traceOrthogonal_hasTraceType
    {n m c : ℕ} {C : QuaternaryAdditiveCode n}
    (hType : C.HasTraceType m c) :
    (traceOrthogonal C).HasTraceType
      (2 * n - m) (n + c - m) := by
  let S := quaternaryToBinarySubspace C
  have hSType : S.HasType m c :=
    hasTraceType_iff_preimage_hasType.mp hType
  let l := Module.finrank (ZMod 2) (symplecticRadical S)
  let D : EASymplecticData n m l c (n + c - m) :=
    { stabilizerSpace := S
      hasType := hSType
      radical_finrank := rfl
      parameter_eq := rfl }
  have hDualBinary := D.symplecticDual_hasType
  have hDualTrace :=
    hasTraceType_binaryToQuaternarySubspace hDualBinary
  change (binaryToQuaternarySubspace
    (NQubitPauliGroupElement.sympOrthogonal S)).HasTraceType
      (2 * n - m) (n + c - m) at hDualTrace
  rw [binaryToQuaternarySubspace_sympOrthogonal S] at hDualTrace
  have hSC : binaryToQuaternarySubspace S = C := by
    exact binaryToQuaternarySubspace_quaternaryToBinarySubspace C
  rw [hSC] at hDualTrace
  exact hDualTrace

end QuaternaryAdditiveCode

end Quaternary
end Quantum
