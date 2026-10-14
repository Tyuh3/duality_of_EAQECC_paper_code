import EAQECC.Basic
import EAQECC.Symplectic.Distance

/-!
将二元辛输入构造的扩展稳定子码封装为纠缠辅助稳定子码，
并从完整对偶定理提取参数与距离推论。
-/

namespace Quantum

/- 将发送端限制与辛坐标投影联系起来，并将候选生成元的冲突秩等同于其辛张成空间的限制辛形式秩。
-/
theorem restrictToBaseGroupElement_binarySymplecticVectorToPauli
    {n c : ℕ} (v : BinarySymplecticVector (n + c)) :
    restrictToBaseGroupElement n c (binarySymplecticVectorToPauli v) =
      binarySymplecticVectorToPauli (baseSymplecticProjection n c v) := by
  apply NQubitPauliGroupElement.ext
  · rfl
  · apply NQubitPauliOperator.toSymplectic_injective
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      calc
        NQubitPauliOperator.toSymplectic
            (restrictToBaseGroupElement n c
              (binarySymplecticVectorToPauli v)).operators
            (Fin.castAdd n i) =
          NQubitPauliOperator.toSymplectic
            (binarySymplecticVectorToPauli v).operators
            (Fin.castAdd (n + c) (Fin.castAdd c i)) := by
              rw [NQubitPauliOperator.toSymplectic_X_part,
                NQubitPauliOperator.toSymplectic_X_part]
              rfl
        _ = v (Fin.castAdd (n + c) (Fin.castAdd c i)) := by
              rw [binarySymplecticVectorToPauli_toSymplectic]
        _ = baseSymplecticProjection n c v (Fin.castAdd n i) := by
              rw [baseSymplecticProjection_X]
        _ = NQubitPauliOperator.toSymplectic
            (binarySymplecticVectorToPauli
              (baseSymplecticProjection n c v)).operators
            (Fin.castAdd n i) := by
              rw [binarySymplecticVectorToPauli_toSymplectic]
    · intro i
      calc
        NQubitPauliOperator.toSymplectic
            (restrictToBaseGroupElement n c
              (binarySymplecticVectorToPauli v)).operators
            (Fin.natAdd n i) =
          NQubitPauliOperator.toSymplectic
            (binarySymplecticVectorToPauli v).operators
            (Fin.natAdd (n + c) (Fin.castAdd c i)) := by
              rw [NQubitPauliOperator.toSymplectic_Z_part,
                NQubitPauliOperator.toSymplectic_Z_part]
              rfl
        _ = v (Fin.natAdd (n + c) (Fin.castAdd c i)) := by
              rw [binarySymplecticVectorToPauli_toSymplectic]
        _ = baseSymplecticProjection n c v (Fin.natAdd n i) := by
              simpa [Fin.natAdd_eq_addNat] using
                (baseSymplecticProjection_Z (c := c) v i).symm
        _ = NQubitPauliOperator.toSymplectic
            (binarySymplecticVectorToPauli
              (baseSymplecticProjection n c v)).operators
            (Fin.natAdd n i) := by
              rw [binarySymplecticVectorToPauli_toSymplectic]

namespace GeneratorListCandidate

theorem conflictRank_eq_symplecticRank_sympSpan
    {n : ℕ} (C : GeneratorListCandidate n) :
    C.conflictRank =
      BinarySymplecticSubspace.symplecticRank
        (NQubitPauliGroupElement.sympSpan C.generatorsList) := by
  let S := NQubitPauliGroupElement.sympSpan C.generatorsList
  have hP : LinearIndependent (ZMod 2)
      (NQubitPauliGroupElement.checkMatrix C.generatorsList) :=
    C.generators_rowsIndependent
  let b : Module.Basis (Fin C.generatorsList.length) (ZMod 2) S :=
    Module.Basis.span hP
  let B := (binarySymplecticBilinForm n).restrict S

  have hGramMatrix :
      LinearMap.BilinForm.toMatrix b B = C.conflictMatrix := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply]
    change binarySymplecticBilinForm n (b i) (b j) =
      NQubitPauliOperator.symplecticInner
        (C.generatorsList.get i).operators
        (C.generatorsList.get j).operators
    rw [show ((b i : S) : BinarySymplecticVector n) =
        NQubitPauliGroupElement.checkMatrix C.generatorsList i by
          exact Module.Basis.coe_span_apply hP i]
    rw [show ((b j : S) : BinarySymplecticVector n) =
        NQubitPauliGroupElement.checkMatrix C.generatorsList j by
          exact Module.Basis.coe_span_apply hP j]
    rw [binarySymplecticBilinForm_apply]
    exact NQubitPauliOperator.symplecticBilinear_toSymplectic _ _

  have hBSymmetric : B.IsSymm := by
    simpa [B] using (binarySymplecticBilinForm_isSymm n).restrict S
  let M : Matrix
      (Fin C.generatorsList.length)
      (Fin C.generatorsList.length) (ZMod 2) :=
    LinearMap.toMatrix b b.dualBasis B
  have hMatrix : M = LinearMap.BilinForm.toMatrix b B := by
    ext i j
    simp only [M, LinearMap.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply,
      Module.Basis.dualBasis_repr]
    exact hBSymmetric.eq (b j) (b i)
  have hMatrixRank :=
    Matrix.rank_eq_finrank_range_toLin M b.dualBasis b
  rw [Matrix.toLin_toMatrix] at hMatrixRank
  unfold GeneratorListCandidate.conflictRank
  unfold BinarySymplecticSubspace.symplecticRank
  rw [show (binarySymplecticBilinForm n).restrict S = B from rfl]
  rw [← hMatrixRank, hMatrix, hGramMatrix]

end GeneratorListCandidate

namespace EASymplecticData

/- 将扩展稳定子生成元限制到发送端。以下证明相位为零、辛向量线性无关及生成元数量关系。
-/
noncomputable def baseGenerators
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    List (NQubitPauliGroupElement n) :=
  A.toStabilizerCode.generatorsList.map
    (restrictToBaseGroupElement n c)

@[simp]
theorem baseGenerators_length
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    A.baseGenerators.length = m := by
  unfold baseGenerators
  rw [List.length_map, A.toStabilizerCode_generators_length]

theorem baseGenerators_phaseZero
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    NQubitPauliGroupElement.AllPhaseZero A.baseGenerators := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g', hg', rfl⟩
  exact A.toStabilizerCode.generators_phaseZero g' hg'

theorem baseGenerators_length_eq_extendedFinrank
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    A.baseGenerators.length =
      Module.finrank (ZMod 2)
        (A.chosenRadicalDecomposition.extendedStabilizerSpace
          A.hasType) := by
  rw [A.baseGenerators_length,
    A.chosenRadicalDecomposition.extendedStabilizerSpace_finrank
      A.hasType]

theorem baseGenerators_checkMatrix_eq
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    NQubitPauliGroupElement.checkMatrix A.baseGenerators =
      (fun i : Fin (Module.finrank (ZMod 2)
          (A.chosenRadicalDecomposition.extendedStabilizerSpace
            A.hasType)) =>
        baseSymplecticProjection n c
          (((A.chosenRadicalDecomposition.extendedStabilizerSpace
              A.hasType).finBasis i :
            A.chosenRadicalDecomposition.extendedStabilizerSpace
              A.hasType) : BinarySymplecticVector (n + c))) ∘
        finCongr A.baseGenerators_length_eq_extendedFinrank := by
  funext i j
  unfold baseGenerators
  simp only [A.toStabilizerCode_generatorsList,
    NQubitPauliGroupElement.checkMatrix, List.get_eq_getElem,
    List.getElem_map, BinarySymplecticSubspace.pauliGeneratorsList,
    List.getElem_ofFn, Function.comp_apply]
  rw [restrictToBaseGroupElement_binarySymplecticVectorToPauli,
    binarySymplecticVectorToPauli_toSymplectic]
  apply congrArg (fun q : Fin (Module.finrank (ZMod 2)
      (A.chosenRadicalDecomposition.extendedStabilizerSpace
        A.hasType)) =>
    baseSymplecticProjection n c
      (((A.chosenRadicalDecomposition.extendedStabilizerSpace
          A.hasType).finBasis q :
        A.chosenRadicalDecomposition.extendedStabilizerSpace
          A.hasType) : BinarySymplecticVector (n + c)) j)
  apply Fin.ext
  rfl

theorem baseProjection_comp_subtype_injective
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    Function.Injective
      ((baseSymplecticProjection n c).comp
        (A.chosenRadicalDecomposition.extendedStabilizerSpace
          A.hasType).subtype) := by
  let T := A.chosenRadicalDecomposition.extendedStabilizerSpace
    A.hasType
  have hRealizes :=
    A.chosenRadicalDecomposition.extendedStabilizerSpace_realizesEAStabilizerSpace
      A.hasType
  intro x y hxy
  have hDifferenceProjection :
      baseSymplecticProjection n c ((x : T) - (y : T)) = 0 := by
    change baseSymplecticProjection n c (x - y) = 0
    have hxy' : baseSymplecticProjection n c x =
        baseSymplecticProjection n c y := hxy
    rw [map_sub, hxy', sub_self]
  have hDifferenceMem :
      ((x : T) - (y : T) : BinarySymplecticVector (n + c)) ∈
        T ⊓ LinearMap.ker (baseSymplecticProjection n c) := by
    exact ⟨Submodule.sub_mem T x.2 y.2,
      LinearMap.mem_ker.mpr hDifferenceProjection⟩
  have hDifferenceZero :
      ((x : T) - (y : T) : BinarySymplecticVector (n + c)) = 0 := by
    rw [hRealizes.2.1] at hDifferenceMem
    simpa using hDifferenceMem
  apply Subtype.ext
  exact sub_eq_zero.mp hDifferenceZero

theorem baseGenerators_rowsLinearIndependent
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    NQubitPauliGroupElement.rowsLinearIndependent A.baseGenerators := by
  let T := A.chosenRadicalDecomposition.extendedStabilizerSpace
    A.hasType
  let f : T →ₗ[ZMod 2] BinarySymplecticVector n :=
    (baseSymplecticProjection n c).comp T.subtype
  have hfKer : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact A.baseProjection_comp_subtype_injective
  have hProjectedBasis : LinearIndependent (ZMod 2)
      (fun i : Fin (Module.finrank (ZMod 2) T) =>
        baseSymplecticProjection n c ((T.finBasis i : T) :
          BinarySymplecticVector (n + c))) := by
    exact T.finBasis.linearIndependent.map' f hfKer
  rw [NQubitPauliGroupElement.rowsLinearIndependent,
    A.baseGenerators_checkMatrix_eq]
  exact (linearIndependent_equiv
    (finCongr A.baseGenerators_length_eq_extendedFinrank)).mpr hProjectedBasis

/- 由发送端生成元组成候选列表。以下证明其辛张成空间为输入 S、冲突秩为 2c、纠缠参数为 c。
-/
noncomputable def baseGeneratorCandidate
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    GeneratorListCandidate n where
  generatorsList := A.baseGenerators
  generators_phaseZero := A.baseGenerators_phaseZero
  generators_rowsIndependent := A.baseGenerators_rowsLinearIndependent

theorem baseGeneratorCandidate_sympSpan
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    NQubitPauliGroupElement.sympSpan
        A.baseGeneratorCandidate.generatorsList =
      A.stabilizerSpace := by
  let T := A.chosenRadicalDecomposition.extendedStabilizerSpace
    A.hasType
  let projectedBasis : Fin (Module.finrank (ZMod 2) T) →
      BinarySymplecticVector n := fun i =>
    baseSymplecticProjection n c
      ((T.finBasis i : T) : BinarySymplecticVector (n + c))
  have hRange :
      Set.range (projectedBasis ∘
          finCongr A.baseGenerators_length_eq_extendedFinrank) =
        Set.range projectedBasis := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨finCongr A.baseGenerators_length_eq_extendedFinrank i, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨(finCongr A.baseGenerators_length_eq_extendedFinrank).symm i, ?_⟩
      simp
  change Submodule.span (ZMod 2)
      (Set.range (NQubitPauliGroupElement.checkMatrix A.baseGenerators)) =
    A.stabilizerSpace
  rw [A.baseGenerators_checkMatrix_eq, hRange]
  calc
    Submodule.span (ZMod 2) (Set.range projectedBasis) =
        Submodule.map (baseSymplecticProjection n c)
          (Submodule.span (ZMod 2) (Set.range fun i =>
            ((T.finBasis i : T) : BinarySymplecticVector (n + c)))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = Submodule.map (baseSymplecticProjection n c) T := by
      congr 1
      calc
        Submodule.span (ZMod 2) (Set.range fun i =>
            ((T.finBasis i : T) : BinarySymplecticVector (n + c))) =
            Submodule.map T.subtype
              (Submodule.span (ZMod 2) (Set.range T.finBasis)) := by
                rw [Submodule.map_span, ← Set.range_comp]
                rfl
        _ = Submodule.map T.subtype ⊤ := by rw [T.finBasis.span_eq]
        _ = T := by
          rw [Submodule.map_top]
          exact T.range_subtype
    _ = T.projectedSpace := rfl
    _ = A.stabilizerSpace :=
      A.chosenRadicalDecomposition.extendedStabilizerSpace_projectedSpace_eq
        A.hasType

theorem baseGeneratorCandidate_conflictRank
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    A.baseGeneratorCandidate.conflictRank = 2 * c := by
  rw [GeneratorListCandidate.conflictRank_eq_symplecticRank_sympSpan,
    A.baseGeneratorCandidate_sympSpan]
  exact A.hasType.2

theorem baseGeneratorCandidate_ebitCount
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    A.baseGeneratorCandidate.ebitCount = c := by
  unfold GeneratorListCandidate.ebitCount
  rw [A.baseGeneratorCandidate_conflictRank]
  omega

/-- 二元辛输入到纠缠辅助稳定子码的构造。
使用发送端候选生成元及已有扩展稳定子码，证明模型要求的参数、纠缠数和限制关系。
-/
noncomputable def toEACode
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    EACode n k c where
  generators := A.baseGeneratorCandidate
  k_add_c_le_n := by
    have hParameters :=
      A.radicalFinrank_add_ebitCount_add_logicalDimension_eq_length
    omega
  generators_length := by
    change A.baseGenerators.length = n + c - k
    unfold baseGenerators
    rw [List.length_map]
    exact A.toStabilizerCode.generators_length
  ebits_minimal := A.baseGeneratorCandidate_ebitCount.symm
  extendedCode := A.toStabilizerCode
  extended_generators_restrict_eq := rfl

@[simp]
theorem toEACode_extendedCode
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    A.toEACode.extendedCode = A.toStabilizerCode := by
  rfl

@[simp]
theorem toEACode_generators
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    A.toEACode.generators = A.baseGeneratorCandidate := by
  rfl

noncomputable def toEACode_canExtendWith
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    CanExtendWith A.toEACode.generators c where
  k' := k
  extendedCode := A.toEACode.extendedCode
  restrict_eq := A.toEACode.extended_generators_restrict_eq

/-- 二元辛空间对偶定理的参数与距离推论。
从完整定理提取参数等式及两侧发送端最小距离，供纠缠辅助码模型调用。
稳定子空间的实现条件与正规化子对应由完整定理给出；此处复用其证明。
-/
theorem symplecticEAQECCDuality
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    k = n + c - m ∧
    k = n - c - l ∧
    (0 < k →
      ∃ d : ℕ,
        A.toEACode.HasDistance d ∧
          HasMinimumSymplecticWeightOutside
            (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace)
            (symplecticRadical A.stabilizerSpace) d) ∧
    (0 < c →
      ∃ d' : ℕ,
        A.symplecticDualData.toEACode.HasDistance d' ∧
          HasMinimumSymplecticWeightOutside A.stabilizerSpace
            (symplecticRadical A.stabilizerSpace) d') := by
  rcases A.symplecticEAQECCDuality_full with
    ⟨⟨hParameter, hAlternativeParameter, hOriginalDistance, _, _⟩,
      ⟨hDualDistance, _, _⟩⟩
  refine ⟨hParameter, hAlternativeParameter, ?_, ?_⟩
  · intro hk
    obtain ⟨d, hDistance, hMinimum⟩ := hOriginalDistance hk
    refine ⟨d, ?_, hMinimum⟩
    exact hDistance
  · intro hc
    obtain ⟨d', hDistance, hMinimum⟩ := hDualDistance hc
    refine ⟨d', ?_, hMinimum⟩
    exact hDistance

end EASymplecticData

end Quantum
