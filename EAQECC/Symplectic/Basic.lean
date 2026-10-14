import QEC.Stabilizer.Framework.Symplectic.SymplecticOrthogonal
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
二元辛子空间的类型、根空间及对偶参数。沿用 QECLean 的二元辛表示，
将辛内积接入 Mathlib 双线性形式，用维数关系推导后续码构造所需的参数。
-/

namespace Quantum

/- 二元辛向量与子空间，以及辛内积的双线性形式表示。
以下证明该形式交替、对称且非退化，并确认两种接口下的正交补一致。
-/
abbrev BinarySymplecticVector (n : ℕ) :=
  Fin (n + n) → ZMod 2

abbrev BinarySymplecticSubspace (n : ℕ) :=
  Submodule (ZMod 2) (BinarySymplecticVector n)

def binarySymplecticBilinForm (n : ℕ) :
    LinearMap.BilinForm (ZMod 2) (BinarySymplecticVector n) :=
  LinearMap.mk₂ (ZMod 2)
    NQubitPauliOperator.symplecticBilinear
    NQubitPauliOperator.symplecticBilinear_add_left
    (by
      intro c v w
      simpa [smul_eq_mul] using
        NQubitPauliOperator.symplecticBilinear_smul_left c v w)
    NQubitPauliOperator.symplecticBilinear_add_right
    (by
      intro c v w
      simpa [smul_eq_mul] using
        NQubitPauliOperator.symplecticBilinear_smul_right c v w)

@[simp]
theorem binarySymplecticBilinForm_apply
    {n : ℕ} (v w : BinarySymplecticVector n) :
    binarySymplecticBilinForm n v w =
      NQubitPauliOperator.symplecticBilinear v w := by
  rfl

theorem binarySymplecticBilinForm_isAlt (n : ℕ) :
    (binarySymplecticBilinForm n).IsAlt := by
  intro v
  simp only [binarySymplecticBilinForm_apply,
    NQubitPauliOperator.symplecticBilinear]
  apply Finset.sum_eq_zero
  intro i _
  have htwo : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  calc
    v (Fin.castAdd n i) * v (Fin.natAdd n i) +
        v (Fin.natAdd n i) * v (Fin.castAdd n i) =
      2 * (v (Fin.castAdd n i) * v (Fin.natAdd n i)) := by ring
    _ = 0 := by rw [htwo, zero_mul]

theorem binarySymplecticBilinForm_isSymm (n : ℕ) :
    (binarySymplecticBilinForm n).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro v w
  simp only [binarySymplecticBilinForm_apply,
    NQubitPauliOperator.symplecticBilinear]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem binarySymplecticBilinForm_nondegenerate (n : ℕ) :
    (binarySymplecticBilinForm n).Nondegenerate := by
  have hLeft : (binarySymplecticBilinForm n).SeparatingLeft := by
    intro v hv
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · let w : BinarySymplecticVector n := fun q =>
        if q = Fin.natAdd n i then 1 else 0
      have hne : ∀ x : Fin n,
          Fin.castAdd n x ≠ Fin.addNat i n := by
        intro x heq
        have hval := congrArg Fin.val heq
        simp [Fin.castAdd] at hval
        omega
      have h := hv w
      simp only [binarySymplecticBilinForm_apply,
        NQubitPauliOperator.symplecticBilinear] at h
      simpa [w, hne, Fin.natAdd_eq_addNat, eq_comm] using h
    · let w : BinarySymplecticVector n := fun q =>
        if q = Fin.castAdd n i then 1 else 0
      have hne : ∀ x : Fin n,
          Fin.addNat x n ≠ Fin.castAdd n i := by
        intro x heq
        have hval := congrArg Fin.val heq
        simp [Fin.castAdd] at hval
        omega
      have h := hv w
      simp only [binarySymplecticBilinForm_apply,
        NQubitPauliOperator.symplecticBilinear] at h
      simpa [w, hne, Fin.natAdd_eq_addNat, eq_comm] using h
  refine ⟨hLeft, ?_⟩
  intro v hv
  apply hLeft v
  intro w
  rw [(binarySymplecticBilinForm_isSymm n).eq]
  exact hv w

namespace BinarySymplecticSubspace

theorem mem_sympOrthogonal_iff_bilinForm
    {n : ℕ} (S : BinarySymplecticSubspace n)
    (v : BinarySymplecticVector n) :
    v ∈ NQubitPauliGroupElement.sympOrthogonal S ↔
      ∀ w ∈ S, binarySymplecticBilinForm n v w = 0 := by
  rfl

theorem sympOrthogonal_eq_bilinForm_orthogonal
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    NQubitPauliGroupElement.sympOrthogonal S =
      (binarySymplecticBilinForm n).orthogonal S := by
  ext v
  constructor
  · intro hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    change binarySymplecticBilinForm n w v = 0
    rw [(binarySymplecticBilinForm_isSymm n).eq w v]
    exact hv w hw
  · intro hv w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
    change binarySymplecticBilinForm n v w = 0
    rw [(binarySymplecticBilinForm_isSymm n).eq v w]
    exact hv w hw

/- 全迷向子空间：其中任意两个向量的辛内积为零，对应生成元两两对易。
-/
def IsTotallyIsotropic {n : ℕ} (S : BinarySymplecticSubspace n) : Prop :=
  S ≤ NQubitPauliGroupElement.sympOrthogonal S

/-- 辛根空间。由同时属于 S 和其辛对偶的向量组成，即 R(S) = S ∩ S⊥。
它包含 S 中与 S 的所有向量辛正交的方向，也是限制辛形式的核所对应的子空间。
-/
def radical {n : ℕ} (S : BinarySymplecticSubspace n) :
    BinarySymplecticSubspace n :=
  S ⊓ NQubitPauliGroupElement.sympOrthogonal S

abbrev _root_.Quantum.symplecticRadical {n : ℕ}
    (S : BinarySymplecticSubspace n) : BinarySymplecticSubspace n :=
  radical S

theorem radical_isTotallyIsotropic
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    IsTotallyIsotropic (radical S) := by
  intro v hv w hw
  exact hv.2 w hw.1

/- 限制辛形式的秩。以下通过核与辛根空间的对应证明秩与根空间维数之和等于子空间维数，
并证明取两次辛对偶恢复原空间、取辛对偶保持根空间。
-/
noncomputable def symplecticRank {n : ℕ} (S : BinarySymplecticSubspace n) : ℕ :=
  Module.finrank (ZMod 2)
    (LinearMap.range ((binarySymplecticBilinForm n).restrict S))

theorem symplecticRank_add_radicalFinrank_eq_finrank
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    S.symplecticRank + Module.finrank (ZMod 2) (radical S) =
      Module.finrank (ZMod 2) S := by
  let B := binarySymplecticBilinForm n
  have hKernelMap :
      (LinearMap.ker (B.restrict S)).map S.subtype = radical S := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxKernel : B.restrict S x = 0 :=
        LinearMap.mem_ker.mp hx
      refine ⟨x.2, ?_⟩
      intro w hw
      change B x w = 0
      have hApply := LinearMap.congr_fun hxKernel ⟨w, hw⟩
      simpa [B] using hApply
    · intro hv
      refine ⟨⟨v, hv.1⟩, ?_, rfl⟩
      change B.restrict S ⟨v, hv.1⟩ = 0
      ext w
      change B v w = 0
      exact hv.2 w w.2
  have hKernelFinrank :
      Module.finrank (ZMod 2) (LinearMap.ker (B.restrict S)) =
        Module.finrank (ZMod 2) (radical S) := by
    rw [← hKernelMap]
    exact (Submodule.finrank_map_subtype_eq S
      (LinearMap.ker (B.restrict S))).symm
  have hRankNullity :=
    LinearMap.finrank_range_add_finrank_ker (B.restrict S)
  change Module.finrank (ZMod 2) (LinearMap.range (B.restrict S)) +
      Module.finrank (ZMod 2) (radical S) =
        Module.finrank (ZMod 2) S
  rw [← hKernelFinrank]
  exact hRankNullity

theorem restrictedBilinForm_nondegenerate_iff_radical_eq_bot
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    ((binarySymplecticBilinForm n).restrict S).Nondegenerate ↔
      S.radical = ⊥ := by
  rw [radical, sympOrthogonal_eq_bilinForm_orthogonal]
  constructor
  · intro hNondegenerate
    exact (LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (binarySymplecticBilinForm_isSymm n).isRefl
      hNondegenerate).inf_eq_bot
  · intro hRadical
    apply LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal
      (binarySymplecticBilinForm n)
      (binarySymplecticBilinForm_isSymm n).isRefl
    rw [disjoint_iff_inf_le, hRadical]

theorem sympOrthogonal_sympOrthogonal
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    NQubitPauliGroupElement.sympOrthogonal
        (NQubitPauliGroupElement.sympOrthogonal S) = S := by
  rw [sympOrthogonal_eq_bilinForm_orthogonal,
    sympOrthogonal_eq_bilinForm_orthogonal]
  exact LinearMap.BilinForm.orthogonal_orthogonal
    (binarySymplecticBilinForm_nondegenerate n)
    (binarySymplecticBilinForm_isSymm n).isRefl S

theorem radical_sympOrthogonal
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    radical (NQubitPauliGroupElement.sympOrthogonal S) = radical S := by
  rw [radical, radical, sympOrthogonal_sympOrthogonal]
  exact inf_comm _ _

/-- 辛类型 [m,c]ₛ。要求 S 的二元维数为 m，限制在 S 上的辛形式秩为 2c。
后续由此证明根空间维数为 m − 2c，以及子空间维数满足 m ≤ n + c。
-/
def HasType {n : ℕ} (S : BinarySymplecticSubspace n)
    (m c : ℕ) : Prop :=
  Module.finrank (ZMod 2) S = m ∧
    S.symplecticRank = 2 * c

theorem radicalFinrank_add_two_mul_eq_of_hasType
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (hType : S.HasType m c) :
    Module.finrank (ZMod 2) (radical S) + 2 * c = m := by
  have hRankNullity := S.symplecticRank_add_radicalFinrank_eq_finrank
  rcases hType with ⟨hDimension, hRank⟩
  omega

theorem dimension_le_length_add_typeParameter_of_hasType
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (hType : S.HasType m c) : m ≤ n + c := by
  have hNondegenerate := binarySymplecticBilinForm_nondegenerate n
  have hOrthogonalDimension :=
    LinearMap.BilinForm.finrank_add_finrank_orthogonal'
      (B := binarySymplecticBilinForm n) S
  have hKernel : LinearMap.ker (binarySymplecticBilinForm n) = ⊥ :=
    hNondegenerate.ker_eq_bot
  rw [hKernel, inf_bot_eq] at hOrthogonalDimension
  simp at hOrthogonalDimension
  let Sorth : BinarySymplecticSubspace n :=
    (binarySymplecticBilinForm n).orthogonal S
  have hLatticeDimension :=
    Submodule.finrank_sup_add_finrank_inf_eq S Sorth
  have hSubspaceLeSup :
      Module.finrank (ZMod 2) S ≤
        Module.finrank (ZMod 2)
          (S ⊔ Sorth : BinarySymplecticSubspace n) :=
    Submodule.finrank_mono
      (show S ≤ (S ⊔ Sorth : BinarySymplecticSubspace n) from le_sup_left)
  have hDimensionBound :
      Module.finrank (ZMod 2) S +
          Module.finrank (ZMod 2) (radical S) ≤ n + n := by
    rw [radical, sympOrthogonal_eq_bilinForm_orthogonal]
    change Module.finrank (ZMod 2) S +
        Module.finrank (ZMod 2)
          (S ⊓ Sorth : BinarySymplecticSubspace n) ≤ n + n
    calc
      Module.finrank (ZMod 2) S +
          Module.finrank (ZMod 2)
            (S ⊓ Sorth : BinarySymplecticSubspace n) ≤
        Module.finrank (ZMod 2)
            (S ⊔ Sorth : BinarySymplecticSubspace n) +
          Module.finrank (ZMod 2)
            (S ⊓ Sorth : BinarySymplecticSubspace n) :=
        Nat.add_le_add_right hSubspaceLeSup _
      _ = Module.finrank (ZMod 2) S +
          Module.finrank (ZMod 2) Sorth := hLatticeDimension
      _ = n + n := hOrthogonalDimension
  have hSubspaceDimension := hType.1
  have hRadicalDimension :=
    radicalFinrank_add_two_mul_eq_of_hasType hType
  omega

end BinarySymplecticSubspace
end Quantum

namespace Quantum

/-- 二元辛输入数据。保存子空间 S、辛类型 [m,c]ₛ、根空间维数 l，
以及输入参数关系 k = n + c − m。l 与 k 受这些条件约束，并非独立自由参数。
l + 2c = m、参数界、合法码构造及距离关系在后续证明中得到。
-/
structure EASymplecticData (n m l c k : ℕ) where
  stabilizerSpace : BinarySymplecticSubspace n
  hasType : stabilizerSpace.HasType m c
  radical_finrank :
    Module.finrank (ZMod 2) (symplecticRadical stabilizerSpace) = l
  parameter_eq : k = n + c - m

namespace EASymplecticData

/- 以下由根空间与限制辛形式的秩推导 l + 2c = m，再结合输入关系推导参数等式和界。
这些界保证后续参数公式中的自然数减法不发生截断。
-/
theorem radicalFinrank_add_two_mul_ebitCount_eq_stabilizerDimension
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    l + 2 * c = m := by
  rw [← D.radical_finrank]
  exact BinarySymplecticSubspace.radicalFinrank_add_two_mul_eq_of_hasType
    D.hasType

theorem stabilizerDimension_le_extendedLength
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    m ≤ n + c :=
  BinarySymplecticSubspace.dimension_le_length_add_typeParameter_of_hasType
    D.hasType

theorem stabilizerDimension_add_logicalDimension_eq_extendedLength
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    m + k = n + c := by
  have hParameter := D.parameter_eq
  have hWellFormed := D.stabilizerDimension_le_extendedLength
  omega

theorem radicalFinrank_add_ebitCount_add_logicalDimension_eq_length
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    l + c + k = n := by
  have hType :=
    D.radicalFinrank_add_two_mul_ebitCount_eq_stabilizerDimension
  have hParameter :=
    D.stabilizerDimension_add_logicalDimension_eq_extendedLength
  omega

theorem logicalDimension_eq_length_sub_ebitCount_sub_radicalFinrank
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    k = n - c - l := by
  have hAccounting :=
    D.radicalFinrank_add_ebitCount_add_logicalDimension_eq_length
  omega

theorem two_mul_ebitCount_le_stabilizerDimension
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    2 * c ≤ m := by
  have hType :=
    D.radicalFinrank_add_two_mul_ebitCount_eq_stabilizerDimension
  omega

theorem parameterBounds
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    2 * c ≤ m ∧ m ≤ n + c :=
  ⟨D.two_mul_ebitCount_le_stabilizerDimension,
    D.stabilizerDimension_le_extendedLength⟩

theorem ebitCount_le_length
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    c ≤ n := by
  have hParameters :=
    D.radicalFinrank_add_ebitCount_add_logicalDimension_eq_length
  omega

theorem stabilizerDimension_le_two_mul_length
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    m ≤ 2 * n := by
  have hSubspace := Submodule.finrank_le D.stabilizerSpace
  rw [D.hasType.1] at hSubspace
  simpa [BinarySymplecticVector, two_mul] using hSubspace

/-- 辛子空间与其辛对偶的类型关系。若 S 具有类型 [m,c]ₛ，
则其辛对偶具有类型 [2n − m,n + c − m]ₛ。证明使用对偶维数与根空间保持关系。
-/
theorem symplecticDual_hasType
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    BinarySymplecticSubspace.HasType
      (NQubitPauliGroupElement.sympOrthogonal D.stabilizerSpace)
      (2 * n - m) (n + c - m) := by
  let S := D.stabilizerSpace
  let Sdual := NQubitPauliGroupElement.sympOrthogonal S
  have hDualDimension :
      Module.finrank (ZMod 2) Sdual = 2 * n - m := by
    rw [show Sdual = NQubitPauliGroupElement.sympOrthogonal S from rfl,
      BinarySymplecticSubspace.sympOrthogonal_eq_bilinForm_orthogonal]
    rw [LinearMap.BilinForm.finrank_orthogonal
      (B := binarySymplecticBilinForm n)
      (binarySymplecticBilinForm_nondegenerate n) S]
    rw [D.hasType.1]
    simp [BinarySymplecticVector]
    omega
  have hDualRankNullity :=
    BinarySymplecticSubspace.symplecticRank_add_radicalFinrank_eq_finrank
      Sdual
  have hSameRadical :
      BinarySymplecticSubspace.radical Sdual =
        BinarySymplecticSubspace.radical S := by
    exact BinarySymplecticSubspace.radical_sympOrthogonal S
  have hRadicalDimension :=
    D.radicalFinrank_add_two_mul_ebitCount_eq_stabilizerDimension
  have hParameterBound := D.stabilizerDimension_le_extendedLength
  have hParameter := D.parameter_eq
  have hAccounting :=
    D.radicalFinrank_add_ebitCount_add_logicalDimension_eq_length
  refine ⟨hDualDimension, ?_⟩
  change BinarySymplecticSubspace.symplecticRank Sdual =
    2 * (n + c - m)
  rw [hSameRadical, D.radical_finrank, hDualDimension] at hDualRankNullity
  omega

/- 以辛对偶为新的输入子空间，保持根空间维数，并交换逻辑维数 k 与纠缠参数 c。
-/
noncomputable def symplecticDualData
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    EASymplecticData n (2 * n - m) l k c where
  stabilizerSpace :=
    NQubitPauliGroupElement.sympOrthogonal D.stabilizerSpace
  hasType := by
    have hDualType := D.symplecticDual_hasType
    rw [← D.parameter_eq] at hDualType
    exact hDualType
  radical_finrank := by
    change Module.finrank (ZMod 2)
      (BinarySymplecticSubspace.radical
        (NQubitPauliGroupElement.sympOrthogonal D.stabilizerSpace)) = l
    rw [BinarySymplecticSubspace.radical_sympOrthogonal]
    exact D.radical_finrank
  parameter_eq := by
    have hType :=
      D.radicalFinrank_add_two_mul_ebitCount_eq_stabilizerDimension
    have hAccounting :=
      D.radicalFinrank_add_ebitCount_add_logicalDimension_eq_length
    have hDimensionBound := D.stabilizerDimension_le_two_mul_length
    omega

@[simp]
theorem symplecticDualData_stabilizerSpace
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    D.symplecticDualData.stabilizerSpace =
      NQubitPauliGroupElement.sympOrthogonal D.stabilizerSpace := by
  rfl

theorem symplecticDualData_hasType
    {n m l c k : ℕ} (D : EASymplecticData n m l c k) :
    D.symplecticDualData.stabilizerSpace.HasType (2 * n - m) k :=
  D.symplecticDualData.hasType

end EASymplecticData
end Quantum

namespace Quantum

/- 将二元辛向量转换为整体相位为零的 Pauli 算子。
后续坐标引理证明转换恢复原辛向量，用于连接子空间与算子条件。
-/
def binarySymplecticVectorToOperator {n : ℕ}
    (v : BinarySymplecticVector n) : NQubitPauliOperator n :=
  fun q =>
    if v (Fin.castAdd n q) = 0 then
      if v (Fin.natAdd n q) = 0 then PauliOperator.I else PauliOperator.Z
    else
      if v (Fin.natAdd n q) = 0 then PauliOperator.X else PauliOperator.Y

def binarySymplecticVectorToPauli {n : ℕ}
    (v : BinarySymplecticVector n) : NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.ofOperator (binarySymplecticVectorToOperator v)

@[simp]
theorem binarySymplecticVectorToPauli_phasePower
    {n : ℕ} (v : BinarySymplecticVector n) :
    (binarySymplecticVectorToPauli v).phasePower = 0 := by
  rfl

@[simp]
theorem binarySymplecticVectorToOperator_toSymplectic_X
    {n : ℕ} (v : BinarySymplecticVector n) (q : Fin n) :
    NQubitPauliOperator.toSymplectic
        (binarySymplecticVectorToOperator v) (Fin.castAdd n q) =
      v (Fin.castAdd n q) := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  by_cases hx : v (Fin.castAdd n q) = 0
  · by_cases hz : v (Fin.addNat q n) = 0 <;>
      simp [binarySymplecticVectorToOperator, hx, hz]
  · have hx_one : v (Fin.castAdd n q) = 1 := by
      generalize hvx : v (Fin.castAdd n q) = x at hx ⊢
      fin_cases x
      · exact (hx rfl).elim
      · rfl
    by_cases hz : v (Fin.addNat q n) = 0 <;>
      simp [binarySymplecticVectorToOperator, hx_one, hz]

@[simp]
theorem binarySymplecticVectorToOperator_toSymplectic_Z
    {n : ℕ} (v : BinarySymplecticVector n) (q : Fin n) :
    NQubitPauliOperator.toSymplectic
        (binarySymplecticVectorToOperator v) (Fin.natAdd n q) =
      v (Fin.natAdd n q) := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  have hindex : Fin.addNat q n = Fin.natAdd n q := by
    apply Fin.ext
    simp [Fin.addNat, Fin.natAdd]
    omega
  rw [← hindex]
  by_cases hz : v (Fin.addNat q n) = 0
  · by_cases hx : v (Fin.castAdd n q) = 0 <;>
      simp [binarySymplecticVectorToOperator, hx, hz]
  · have hz_one : v (Fin.addNat q n) = 1 := by
      generalize hvz : v (Fin.addNat q n) = z at hz ⊢
      fin_cases z
      · exact (hz rfl).elim
      · rfl
    by_cases hx : v (Fin.castAdd n q) = 0 <;>
      simp [binarySymplecticVectorToOperator, hx, hz_one]

@[simp]
theorem binarySymplecticVectorToOperator_toSymplectic
    {n : ℕ} (v : BinarySymplecticVector n) :
    NQubitPauliOperator.toSymplectic
        (binarySymplecticVectorToOperator v) = v := by
  funext j
  exact Fin.addCases
    (binarySymplecticVectorToOperator_toSymplectic_X v)
    (binarySymplecticVectorToOperator_toSymplectic_Z v)
    j

@[simp]
theorem binarySymplecticVectorToPauli_toSymplectic
    {n : ℕ} (v : BinarySymplecticVector n) :
    NQubitPauliOperator.toSymplectic
        (binarySymplecticVectorToPauli v).operators = v := by
  exact binarySymplecticVectorToOperator_toSymplectic v

@[simp]
theorem binarySymplecticVectorToOperator_toSymplectic_inverse
    {n : ℕ} (op : NQubitPauliOperator n) :
    binarySymplecticVectorToOperator
        (NQubitPauliOperator.toSymplectic op) = op := by
  apply NQubitPauliOperator.toSymplectic_injective
  rw [binarySymplecticVectorToOperator_toSymplectic]

end Quantum
