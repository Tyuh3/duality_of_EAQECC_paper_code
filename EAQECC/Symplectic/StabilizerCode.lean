import EAQECC.Symplectic.Construction
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
从全迷向扩展子空间构造普通稳定子码。选取基并转换为 Pauli 生成元，
证明稳定子群合法，构造逻辑算子，再确定发送端正规化子的辛空间表示。
-/

namespace Quantum
namespace BinarySymplecticSubspace

/- 选取子空间的有限基并转换为 Pauli 生成元。以下证明生成元线性无关、相位为零且张成原空间。
-/
noncomputable abbrev finBasis
    {n : ℕ} (T : BinarySymplecticSubspace n) :=
  Module.finBasis (ZMod 2) T

noncomputable def pauliGeneratorsList
    {n : ℕ} (T : BinarySymplecticSubspace n) :
    List (NQubitPauliGroupElement n) :=
  List.ofFn fun i : Fin (Module.finrank (ZMod 2) T) =>
    binarySymplecticVectorToPauli
      ((T.finBasis i : T) : BinarySymplecticVector n)

@[simp]
theorem pauliGeneratorsList_length
    {n : ℕ} (T : BinarySymplecticSubspace n) :
    T.pauliGeneratorsList.length = Module.finrank (ZMod 2) T := by
  simp [pauliGeneratorsList]

theorem pauliGeneratorsList_checkMatrix_eq
    {n : ℕ} (T : BinarySymplecticSubspace n) :
    NQubitPauliGroupElement.checkMatrix T.pauliGeneratorsList =
      (fun i : Fin (Module.finrank (ZMod 2) T) =>
        ((T.finBasis i : T) : BinarySymplecticVector n)) ∘
        finCongr (T.pauliGeneratorsList_length) := by
  funext i j
  unfold NQubitPauliGroupElement.checkMatrix
  simp only [pauliGeneratorsList, List.get_ofFn, Function.comp_apply]
  rw [binarySymplecticVectorToPauli_toSymplectic]
  apply congrArg (fun a : Fin (Module.finrank (ZMod 2) T) =>
    ((T.finBasis a : T) : BinarySymplecticVector n) j)
  apply Fin.ext
  rfl

theorem pauliGeneratorsList_rowsLinearIndependent
    {n : ℕ} (T : BinarySymplecticSubspace n) :
    NQubitPauliGroupElement.rowsLinearIndependent T.pauliGeneratorsList := by
  rw [NQubitPauliGroupElement.rowsLinearIndependent,
    T.pauliGeneratorsList_checkMatrix_eq]
  apply (linearIndependent_equiv
    (finCongr T.pauliGeneratorsList_length)).mpr
  exact T.finBasis.linearIndependent.map' T.subtype T.ker_subtype

theorem pauliGeneratorsList_sympSpan_eq
    {n : ℕ} (T : BinarySymplecticSubspace n) :
    NQubitPauliGroupElement.sympSpan T.pauliGeneratorsList = T := by
  rw [NQubitPauliGroupElement.sympSpan,
    T.pauliGeneratorsList_checkMatrix_eq]
  have hRange :
      Set.range
          ((fun i : Fin (Module.finrank (ZMod 2) T) =>
            ((T.finBasis i : T) : BinarySymplecticVector n)) ∘
            finCongr T.pauliGeneratorsList_length) =
        Set.range (fun i : Fin (Module.finrank (ZMod 2) T) =>
          ((T.finBasis i : T) : BinarySymplecticVector n)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨finCongr T.pauliGeneratorsList_length i, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨(finCongr T.pauliGeneratorsList_length).symm i, ?_⟩
      simp
  rw [hRange]
  calc
    Submodule.span (ZMod 2) (Set.range fun i =>
        ((T.finBasis i : T) : BinarySymplecticVector n)) =
        Submodule.map T.subtype
          (Submodule.span (ZMod 2) (Set.range T.finBasis)) := by
            rw [Submodule.map_span, ← Set.range_comp]
            rfl
    _ = Submodule.map T.subtype ⊤ := by rw [T.finBasis.span_eq]
    _ = LinearMap.range T.subtype := Submodule.map_top _
    _ = T := T.range_subtype

theorem pauliGeneratorsList_phaseZero
    {n : ℕ} (T : BinarySymplecticSubspace n) :
    NQubitPauliGroupElement.AllPhaseZero T.pauliGeneratorsList := by
  apply NQubitPauliGroupElement.AllPhaseZero_ofFn
  intro i
  exact binarySymplecticVectorToPauli_phasePower _

/- 全迷向性保证生成元对易；结合线性无关性证明生成群不含负恒等算子。
-/
theorem pauliGeneratorsList_commute
    {n : ℕ} (T : BinarySymplecticSubspace n)
    (hIsotropic : T.IsTotallyIsotropic) :
    ∀ g ∈ NQubitPauliGroupElement.listToSet T.pauliGeneratorsList,
      ∀ h ∈ NQubitPauliGroupElement.listToSet T.pauliGeneratorsList,
        g * h = h * g := by
  intro g hg h hh
  rw [NQubitPauliGroupElement.listToSet] at hg hh
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hh
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero,
    ← NQubitPauliOperator.symplecticBilinear_toSymplectic]
  let i' : Fin (Module.finrank (ZMod 2) T) :=
    Fin.cast T.pauliGeneratorsList_length i
  let j' : Fin (Module.finrank (ZMod 2) T) :=
    Fin.cast T.pauliGeneratorsList_length j
  have hPair := (hIsotropic (T.finBasis i').2)
    ((T.finBasis j' : T) : BinarySymplecticVector n) (T.finBasis j').2
  simpa [pauliGeneratorsList, i', j'] using hPair

theorem negIdentity_not_mem_closure_pauliGeneratorsList
    {n : ℕ} (T : BinarySymplecticSubspace n)
    (hIsotropic : T.IsTotallyIsotropic) :
    StabilizerGroup.negIdentity n ∉
      Subgroup.closure
        (NQubitPauliGroupElement.listToSet T.pauliGeneratorsList) :=
  NQubitPauliGroupElement.negIdentity_not_mem_of_indep_phase_zero_commute
    T.pauliGeneratorsList
    T.pauliGeneratorsList_phaseZero
    T.pauliGeneratorsList_rowsLinearIndependent
    (T.pauliGeneratorsList_commute hIsotropic)

/- 由上述生成元构造稳定子群。后续将与群中元素对易的条件转化为辛正交条件。
-/
noncomputable def toStabilizerGroup
    {n : ℕ} (T : BinarySymplecticSubspace n)
    (hIsotropic : T.IsTotallyIsotropic) : StabilizerGroup n :=
  StabilizerGroup.mkStabilizerFromGenerators n T.pauliGeneratorsList
    (T.pauliGeneratorsList_commute hIsotropic)
    (T.negIdentity_not_mem_closure_pauliGeneratorsList hIsotropic)

@[simp]
theorem toStabilizerGroup_toSubgroup
    {n : ℕ} (T : BinarySymplecticSubspace n)
    (hIsotropic : T.IsTotallyIsotropic) :
    (T.toStabilizerGroup hIsotropic).toSubgroup =
      Subgroup.closure
        (NQubitPauliGroupElement.listToSet T.pauliGeneratorsList) := by
  rfl

theorem mem_toStabilizerGroup_centralizer_iff
    {n : ℕ} (T : BinarySymplecticSubspace n)
    (hIsotropic : T.IsTotallyIsotropic)
    (g : NQubitPauliGroupElement n) :
    g ∈ StabilizerGroup.centralizer (T.toStabilizerGroup hIsotropic) ↔
      NQubitPauliOperator.toSymplectic g.operators ∈
        NQubitPauliGroupElement.sympOrthogonal T := by
  rw [StabilizerGroup.mem_centralizer_iff_closure g
    (T.toStabilizerGroup hIsotropic)
    (NQubitPauliGroupElement.listToSet T.pauliGeneratorsList) rfl]
  have hOrth :=
    NQubitPauliGroupElement.mem_sympOrthogonal_sympSpan_iff
      T.pauliGeneratorsList g.operators
  rw [T.pauliGeneratorsList_sympSpan_eq] at hOrth
  rw [hOrth]
  constructor
  · intro h p hp
    exact (NQubitPauliOperator.commutes_iff_symplectic_inner_zero g p).mp
      (h p (by
        rw [NQubitPauliGroupElement.listToSet]
        exact hp)).symm
  · intro h p hp
    exact ((NQubitPauliOperator.commutes_iff_symplectic_inner_zero g p).mpr
      (h p (by
        rw [NQubitPauliGroupElement.listToSet] at hp
        exact hp))).symm

theorem mem_toStabilizerGroup_pauliNormalizer_iff
    {n : ℕ} (T : BinarySymplecticSubspace n)
    (hIsotropic : T.IsTotallyIsotropic)
    (g : NQubitPauliGroupElement n) :
    g ∈ StabilizerGroup.pauliNormalizer (T.toStabilizerGroup hIsotropic) ↔
      NQubitPauliOperator.toSymplectic g.operators ∈
        NQubitPauliGroupElement.sympOrthogonal T := by
  rw [StabilizerGroup.pauliNormalizer_eq_centralizer]
  exact T.mem_toStabilizerGroup_centralizer_iff hIsotropic g

/- Pauli 算子的对易与反对易判定，分别对应二元辛内积为零与一。
-/
theorem binarySymplecticVectorToPauli_commutes_iff
    {n : ℕ} (v w : BinarySymplecticVector n) :
    binarySymplecticVectorToPauli v * binarySymplecticVectorToPauli w =
        binarySymplecticVectorToPauli w * binarySymplecticVectorToPauli v ↔
      NQubitPauliOperator.symplecticBilinear v w = 0 := by
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero,
    ← NQubitPauliOperator.symplecticBilinear_toSymplectic]
  simp

theorem binarySymplecticVectorToPauli_anticommutes_iff
    {n : ℕ} (v w : BinarySymplecticVector n) :
    NQubitPauliGroupElement.Anticommute
        (binarySymplecticVectorToPauli v)
        (binarySymplecticVectorToPauli w) ↔
      NQubitPauliOperator.symplecticBilinear v w = 1 := by
  rw [NQubitPauliOperator.anticommutes_iff_symplectic_inner_one,
    ← NQubitPauliOperator.symplecticBilinear_toSymplectic]
  simp

theorem binarySymplecticVectorToPauli_baseEmbedding_commutes_iff
    {n c : ℕ} (v w : BinarySymplecticVector n) :
    binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) *
          binarySymplecticVectorToPauli (baseSymplecticEmbedding n c w) =
        binarySymplecticVectorToPauli (baseSymplecticEmbedding n c w) *
          binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) ↔
      NQubitPauliOperator.symplecticBilinear v w = 0 := by
  rw [binarySymplecticVectorToPauli_commutes_iff,
    symplecticBilinear_embedding]

theorem binarySymplecticVectorToPauli_baseEmbedding_anticommutes_iff
    {n c : ℕ} (v w : BinarySymplecticVector n) :
    NQubitPauliGroupElement.Anticommute
        (binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v))
        (binarySymplecticVectorToPauli (baseSymplecticEmbedding n c w)) ↔
      NQubitPauliOperator.symplecticBilinear v w = 1 := by
  rw [binarySymplecticVectorToPauli_anticommutes_iff,
    symplecticBilinear_embedding]

namespace RadicalDecomposition

noncomputable def extendedStabilizerGroup
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    StabilizerGroup (n + c) :=
  (D.extendedStabilizerSpace hType).toStabilizerGroup
    (D.extendedStabilizerSpace_isTotallyIsotropic hType)

theorem extendedStabilizerGroup_generators_length
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    (D.extendedStabilizerSpace hType).pauliGeneratorsList.length = m := by
  rw [pauliGeneratorsList_length,
    D.extendedStabilizerSpace_finrank hType]

theorem extendedStabilizerGroup_sympSpan_eq
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    NQubitPauliGroupElement.sympSpan
        (D.extendedStabilizerSpace hType).pauliGeneratorsList =
      D.extendedStabilizerSpace hType :=
  (D.extendedStabilizerSpace hType).pauliGeneratorsList_sympSpan_eq

theorem basePauli_mem_extendedStabilizerGroup_pauliNormalizer_iff
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c)
    (v : BinarySymplecticVector n) :
    binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) ∈
        StabilizerGroup.pauliNormalizer
          (D.extendedStabilizerGroup hType) ↔
      v ∈ NQubitPauliGroupElement.sympOrthogonal S := by
  rw [extendedStabilizerGroup,
    BinarySymplecticSubspace.mem_toStabilizerGroup_pauliNormalizer_iff,
    binarySymplecticVectorToPauli_toSymplectic]
  exact RealizesEAStabilizerSpace.baseEmbedding_mem_sympOrthogonal_iff
    (D.extendedStabilizerSpace_realizesEAStabilizerSpace hType) v

end RadicalDecomposition

end BinarySymplecticSubspace
end Quantum

namespace Quantum
namespace EASymplecticData

/- 为输入数据选取根空间分解和逻辑部分分解，并构造相应扩展稳定子群。
-/
noncomputable abbrev chosenRadicalDecomposition
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :=
  BinarySymplecticSubspace.radicalDecomposition A.stabilizerSpace

noncomputable abbrev chosenLogicalDecomposition
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :=
  BinarySymplecticSubspace.logicalDecomposition A.stabilizerSpace

noncomputable def extendedStabilizerGroup
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    StabilizerGroup (n + c) :=
  A.chosenRadicalDecomposition.extendedStabilizerGroup A.hasType

/- 从逻辑部分的标准辛基选取逻辑 X、Z 向量。
以下证明同一逻辑比特的两个方向反对易，不同逻辑比特的方向对易。
-/
noncomputable def logicalXVector
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) : BinarySymplecticVector n :=
  (((A.chosenLogicalDecomposition.logicalPairBasis A).basis (Sum.inl i) :
      A.chosenLogicalDecomposition.logicalPart) : BinarySymplecticVector n)

noncomputable def logicalZVector
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) : BinarySymplecticVector n :=
  (((A.chosenLogicalDecomposition.logicalPairBasis A).basis (Sum.inr i) :
      A.chosenLogicalDecomposition.logicalPart) : BinarySymplecticVector n)

theorem logicalXVector_mem_symplecticDual
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) :
    A.logicalXVector i ∈
      NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace := by
  exact A.chosenLogicalDecomposition.logicalPart_le_symplecticDual
    ((A.chosenLogicalDecomposition.logicalPairBasis A).basis (Sum.inl i)).2

theorem logicalZVector_mem_symplecticDual
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) :
    A.logicalZVector i ∈
      NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace := by
  exact A.chosenLogicalDecomposition.logicalPart_le_symplecticDual
    ((A.chosenLogicalDecomposition.logicalPairBasis A).basis (Sum.inr i)).2

theorem symplecticBilinear_logicalXVector_logicalZVector
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) :
    NQubitPauliOperator.symplecticBilinear
      (A.logicalXVector i) (A.logicalZVector i) = 1 := by
  simpa [logicalXVector, logicalZVector] using
    (A.chosenLogicalDecomposition.logicalPairBasis A).left_right i i

theorem symplecticBilinear_logicalXVector_logicalXVector
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i j : Fin k) :
    NQubitPauliOperator.symplecticBilinear
      (A.logicalXVector i) (A.logicalXVector j) = 0 := by
  exact (A.chosenLogicalDecomposition.logicalPairBasis A).left_left i j

theorem symplecticBilinear_logicalZVector_logicalZVector
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i j : Fin k) :
    NQubitPauliOperator.symplecticBilinear
      (A.logicalZVector i) (A.logicalZVector j) = 0 := by
  exact (A.chosenLogicalDecomposition.logicalPairBasis A).right_right i j

theorem symplecticBilinear_logicalXVector_logicalZVector_eq_zero
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    {i j : Fin k} (hij : i ≠ j) :
    NQubitPauliOperator.symplecticBilinear
      (A.logicalXVector i) (A.logicalZVector j) = 0 := by
  simpa [logicalXVector, logicalZVector, hij] using
    (A.chosenLogicalDecomposition.logicalPairBasis A).left_right i j

theorem symplecticBilinear_logicalZVector_logicalXVector_eq_zero
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    {i j : Fin k} (hij : i ≠ j) :
    NQubitPauliOperator.symplecticBilinear
      (A.logicalZVector i) (A.logicalXVector j) = 0 := by
  have hSymm :
      ((binarySymplecticBilinForm n).restrict
        A.chosenLogicalDecomposition.logicalPart).IsSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro v w
    exact (binarySymplecticBilinForm_isSymm n).eq v w
  simpa [logicalXVector, logicalZVector, hij] using
    (A.chosenLogicalDecomposition.logicalPairBasis A).right_left hSymm i j

/- 将逻辑辛向量转换为 Pauli 算子，得到稳定子码所需的逻辑算子及其对易关系。
-/
noncomputable def logicalXPauli
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) : NQubitPauliGroupElement (n + c) :=
  binarySymplecticVectorToPauli
    (baseSymplecticEmbedding n c (A.logicalXVector i))

noncomputable def logicalZPauli
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) : NQubitPauliGroupElement (n + c) :=
  binarySymplecticVectorToPauli
    (baseSymplecticEmbedding n c (A.logicalZVector i))

theorem logicalXPauli_mem_centralizer
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) :
    A.logicalXPauli i ∈ StabilizerGroup.centralizer A.extendedStabilizerGroup := by
  rw [← StabilizerGroup.pauliNormalizer_eq_centralizer]
  exact (BinarySymplecticSubspace.RadicalDecomposition.basePauli_mem_extendedStabilizerGroup_pauliNormalizer_iff
      A.chosenRadicalDecomposition A.hasType (A.logicalXVector i)).mpr
    (A.logicalXVector_mem_symplecticDual i)

theorem logicalZPauli_mem_centralizer
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) :
    A.logicalZPauli i ∈ StabilizerGroup.centralizer A.extendedStabilizerGroup := by
  rw [← StabilizerGroup.pauliNormalizer_eq_centralizer]
  exact (BinarySymplecticSubspace.RadicalDecomposition.basePauli_mem_extendedStabilizerGroup_pauliNormalizer_iff
      A.chosenRadicalDecomposition A.hasType (A.logicalZVector i)).mpr
    (A.logicalZVector_mem_symplecticDual i)

theorem logicalXPauli_anticommutes_logicalZPauli
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) :
    NQubitPauliGroupElement.Anticommute
      (A.logicalXPauli i) (A.logicalZPauli i) := by
  rw [logicalXPauli, logicalZPauli,
    BinarySymplecticSubspace.binarySymplecticVectorToPauli_baseEmbedding_anticommutes_iff]
  exact A.symplecticBilinear_logicalXVector_logicalZVector i

noncomputable def logicalQubitOps
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i : Fin k) :
    StabilizerGroup.LogicalQubitOps (n + c) A.extendedStabilizerGroup where
  xOp := A.logicalXPauli i
  zOp := A.logicalZPauli i
  x_mem_centralizer := A.logicalXPauli_mem_centralizer i
  z_mem_centralizer := A.logicalZPauli_mem_centralizer i
  anticommute := A.logicalXPauli_anticommutes_logicalZPauli i

theorem logicalPaulis_commute_cross
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (i j : Fin k) (hij : i ≠ j) :
    (A.logicalQubitOps i).xOp * (A.logicalQubitOps j).xOp =
        (A.logicalQubitOps j).xOp * (A.logicalQubitOps i).xOp ∧
      (A.logicalQubitOps i).xOp * (A.logicalQubitOps j).zOp =
        (A.logicalQubitOps j).zOp * (A.logicalQubitOps i).xOp ∧
      (A.logicalQubitOps i).zOp * (A.logicalQubitOps j).xOp =
        (A.logicalQubitOps j).xOp * (A.logicalQubitOps i).zOp ∧
      (A.logicalQubitOps i).zOp * (A.logicalQubitOps j).zOp =
        (A.logicalQubitOps j).zOp * (A.logicalQubitOps i).zOp := by
  change
    A.logicalXPauli i * A.logicalXPauli j =
        A.logicalXPauli j * A.logicalXPauli i ∧
      A.logicalXPauli i * A.logicalZPauli j =
        A.logicalZPauli j * A.logicalXPauli i ∧
      A.logicalZPauli i * A.logicalXPauli j =
        A.logicalXPauli j * A.logicalZPauli i ∧
      A.logicalZPauli i * A.logicalZPauli j =
        A.logicalZPauli j * A.logicalZPauli i
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [logicalXPauli, logicalXPauli,
      BinarySymplecticSubspace.binarySymplecticVectorToPauli_baseEmbedding_commutes_iff]
    exact A.symplecticBilinear_logicalXVector_logicalXVector i j
  · rw [logicalXPauli, logicalZPauli,
      BinarySymplecticSubspace.binarySymplecticVectorToPauli_baseEmbedding_commutes_iff]
    exact A.symplecticBilinear_logicalXVector_logicalZVector_eq_zero hij
  · rw [logicalZPauli, logicalXPauli,
      BinarySymplecticSubspace.binarySymplecticVectorToPauli_baseEmbedding_commutes_iff]
    exact A.symplecticBilinear_logicalZVector_logicalXVector_eq_zero hij
  · rw [logicalZPauli, logicalZPauli,
      BinarySymplecticSubspace.binarySymplecticVectorToPauli_baseEmbedding_commutes_iff]
    exact A.symplecticBilinear_logicalZVector_logicalZVector i j

theorem logicalDimension_le_extendedLength
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    k ≤ n + c := by
  have hParameters :=
    A.stabilizerDimension_add_logicalDimension_eq_extendedLength
  omega

theorem extendedGenerators_length_eq_extendedLength_sub_logicalDimension
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    (A.chosenRadicalDecomposition.extendedStabilizerSpace A.hasType).pauliGeneratorsList.length =
      (n + c) - k := by
  have hLength :=
    BinarySymplecticSubspace.RadicalDecomposition.extendedStabilizerGroup_generators_length
      A.chosenRadicalDecomposition A.hasType
  have hParameters :=
    A.stabilizerDimension_add_logicalDimension_eq_extendedLength
  omega

/-- 由二元辛输入构造扩展稳定子码。辅助扩展保证稳定子生成元对易，
逻辑部分提供 k 对逻辑算子；后续证明发送端正规化子对应 S 的辛对偶。
-/
noncomputable def toStabilizerCode
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    StabilizerGroup.StabilizerCode (n + c) k := by
  let T := A.chosenRadicalDecomposition.extendedStabilizerSpace A.hasType
  have hIsotropic : T.IsTotallyIsotropic :=
    BinarySymplecticSubspace.RadicalDecomposition.extendedStabilizerSpace_isTotallyIsotropic
      A.chosenRadicalDecomposition A.hasType
  let generators := T.pauliGeneratorsList
  have hCommute :
      ∀ g ∈ NQubitPauliGroupElement.listToSet generators,
        ∀ h ∈ NQubitPauliGroupElement.listToSet generators,
          g * h = h * g :=
    T.pauliGeneratorsList_commute hIsotropic
  have hNoNeg : StabilizerGroup.negIdentity (n + c) ∉
      Subgroup.closure
        (NQubitPauliGroupElement.listToSet generators) :=
    T.negIdentity_not_mem_closure_pauliGeneratorsList hIsotropic
  refine {
    hk := A.logicalDimension_le_extendedLength
    generatorsList := generators
    generators_length := ?_
    generators_phaseZero := T.pauliGeneratorsList_phaseZero
    generators_independent :=
      StabilizerGroup.GeneratorsIndependent_of_rowsLinearIndependent
        (n + c) generators T.pauliGeneratorsList_rowsLinearIndependent
    generators_commute := hCommute
    closure_no_neg_identity := hNoNeg
    logicalOps := ?_
    logical_commute_cross := ?_ }
  · exact A.extendedGenerators_length_eq_extendedLength_sub_logicalDimension
  · intro i
    exact A.logicalQubitOps i
  · intro i j hij
    exact A.logicalPaulis_commute_cross i j hij

@[simp]
theorem toStabilizerCode_generatorsList
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    A.toStabilizerCode.generatorsList =
      (A.chosenRadicalDecomposition.extendedStabilizerSpace A.hasType).pauliGeneratorsList := by
  rfl

theorem toStabilizerCode_generators_length
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    A.toStabilizerCode.generatorsList.length = m := by
  rw [A.toStabilizerCode_generatorsList]
  exact BinarySymplecticSubspace.RadicalDecomposition.extendedStabilizerGroup_generators_length
    A.chosenRadicalDecomposition A.hasType

@[simp]
theorem toStabilizerCode_toStabilizerGroup
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    A.toStabilizerCode.toStabilizerGroup = A.extendedStabilizerGroup := by
  rfl

theorem toStabilizerCode_generators_sympSpan_eq_extendedStabilizerSpace
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    NQubitPauliGroupElement.sympSpan A.toStabilizerCode.generatorsList =
      A.chosenRadicalDecomposition.extendedStabilizerSpace A.hasType := by
  rw [A.toStabilizerCode_generatorsList]
  exact BinarySymplecticSubspace.pauliGeneratorsList_sympSpan_eq
    (A.chosenRadicalDecomposition.extendedStabilizerSpace A.hasType)

theorem basePauli_mem_toStabilizerCode_pauliNormalizer_iff
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (v : BinarySymplecticVector n) :
    binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) ∈
        StabilizerGroup.pauliNormalizer A.toStabilizerCode.toStabilizerGroup ↔
      v ∈ NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace := by
  rw [A.toStabilizerCode_toStabilizerGroup]
  exact BinarySymplecticSubspace.RadicalDecomposition.basePauli_mem_extendedStabilizerGroup_pauliNormalizer_iff
    A.chosenRadicalDecomposition A.hasType v

/-- 将同一构造应用于辛对偶输入，得到辅助量子比特数为 k、逻辑量子比特数为 c 的对偶码。
后续证明其发送端正规化子对应原空间 S。
-/
noncomputable def toDualStabilizerCode
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    StabilizerGroup.StabilizerCode (n + k) c :=
  A.symplecticDualData.toStabilizerCode

theorem toDualStabilizerCode_generators_length
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    A.toDualStabilizerCode.generatorsList.length = 2 * n - m := by
  change A.symplecticDualData.toStabilizerCode.generatorsList.length =
    2 * n - m
  rw [A.symplecticDualData.toStabilizerCode_generatorsList]
  exact BinarySymplecticSubspace.RadicalDecomposition.extendedStabilizerGroup_generators_length
    A.symplecticDualData.chosenRadicalDecomposition
    A.symplecticDualData.hasType

theorem dualExtendedStabilizerSpace_realizes_symplecticDual
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    RealizesEAStabilizerSpace
      (BinarySymplecticSubspace.RadicalDecomposition.extendedStabilizerSpace
        A.symplecticDualData.chosenRadicalDecomposition
        A.symplecticDualData.hasType)
      (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace) := by
  simpa using
    (BinarySymplecticSubspace.RadicalDecomposition.extendedStabilizerSpace_realizesEAStabilizerSpace
      A.symplecticDualData.chosenRadicalDecomposition
      A.symplecticDualData.hasType)

theorem basePauli_mem_toDualStabilizerCode_pauliNormalizer_iff
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (v : BinarySymplecticVector n) :
    binarySymplecticVectorToPauli (baseSymplecticEmbedding n k v) ∈
        StabilizerGroup.pauliNormalizer
          A.toDualStabilizerCode.toStabilizerGroup ↔
      v ∈ A.stabilizerSpace := by
  change binarySymplecticVectorToPauli (baseSymplecticEmbedding n k v) ∈
      StabilizerGroup.pauliNormalizer
        A.symplecticDualData.toStabilizerCode.toStabilizerGroup ↔
    v ∈ A.stabilizerSpace
  rw [A.symplecticDualData.toStabilizerCode_toStabilizerGroup]
  have hNormalizer :=
    BinarySymplecticSubspace.RadicalDecomposition.basePauli_mem_extendedStabilizerGroup_pauliNormalizer_iff
      A.symplecticDualData.chosenRadicalDecomposition
      A.symplecticDualData.hasType v
  refine hNormalizer.trans ?_
  rw [A.symplecticDualData_stabilizerSpace,
    BinarySymplecticSubspace.sympOrthogonal_sympOrthogonal]

end EASymplecticData
end Quantum
