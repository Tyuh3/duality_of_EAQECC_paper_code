import EAQECC.Distance
import EAQECC.Symplectic.StabilizerCode

/-!
二元辛表示下的重量与发送端距离。证明非平凡逻辑算子对应辛对偶或原空间中根空间之外的向量，
并汇总完整的二元辛空间纠缠辅助码对偶定理。
-/

namespace Quantum

/- 辛支集与辛重量。一个量子比特的 X、Z 坐标至少有一个非零时，该坐标计入支集。
以下证明辛重量等于相应 Pauli 算子的重量，并在辅助端补零后保持不变。
-/
def symplecticSupport {n : ℕ}
    (v : BinarySymplecticVector n) : Finset (Fin n) :=
  Finset.univ.filter fun q =>
    v (Fin.castAdd n q) ≠ 0 ∨ v (Fin.natAdd n q) ≠ 0

def symplecticWeight {n : ℕ}
    (v : BinarySymplecticVector n) : ℕ :=
  (symplecticSupport v).card

@[simp]
theorem mem_symplecticSupport_iff
    {n : ℕ} (v : BinarySymplecticVector n) (q : Fin n) :
    q ∈ symplecticSupport v ↔
      v (Fin.castAdd n q) ≠ 0 ∨ v (Fin.natAdd n q) ≠ 0 := by
  simp [symplecticSupport]

theorem binarySymplecticVectorToOperator_apply_eq_I_iff
    {n : ℕ} (v : BinarySymplecticVector n) (q : Fin n) :
    binarySymplecticVectorToOperator v q = PauliOperator.I ↔
      v (Fin.castAdd n q) = 0 ∧ v (Fin.natAdd n q) = 0 := by
  have hindex : Fin.addNat q n = Fin.natAdd n q := by
    apply Fin.ext
    simp [Fin.addNat, Fin.natAdd]
    omega
  rw [← hindex]
  by_cases hx : v (Fin.castAdd n q) = 0 <;>
    by_cases hz : v (Fin.addNat q n) = 0 <;>
      simp [binarySymplecticVectorToOperator, hx, hz]

theorem binarySymplecticVectorToOperator_support
    {n : ℕ} (v : BinarySymplecticVector n) :
    NQubitPauliOperator.support (binarySymplecticVectorToOperator v) =
      symplecticSupport v := by
  ext q
  rw [NQubitPauliOperator.mem_support, mem_symplecticSupport_iff]
  constructor
  · intro hOperator
    apply not_and_or.mp
    intro hCoordinates
    exact hOperator
      ((binarySymplecticVectorToOperator_apply_eq_I_iff v q).mpr hCoordinates)
  · intro hCoordinates hOperator
    have hZero :=
      (binarySymplecticVectorToOperator_apply_eq_I_iff v q).mp hOperator
    rcases hCoordinates with hx | hz
    · exact hx hZero.1
    · exact hz hZero.2

@[simp]
theorem binarySymplecticVectorToOperator_weight
    {n : ℕ} (v : BinarySymplecticVector n) :
    NQubitPauliOperator.weight (binarySymplecticVectorToOperator v) =
      symplecticWeight v := by
  rw [NQubitPauliOperator.weight, symplecticWeight,
    binarySymplecticVectorToOperator_support]

theorem symplecticWeight_toSymplectic
    {n : ℕ} (op : NQubitPauliOperator n) :
    symplecticWeight (NQubitPauliOperator.toSymplectic op) =
      NQubitPauliOperator.weight op := by
  rw [← binarySymplecticVectorToOperator_weight,
    binarySymplecticVectorToOperator_toSymplectic_inverse]

theorem symplecticWeight_eq_zero_iff
    {n : ℕ} (v : BinarySymplecticVector n) :
    symplecticWeight v = 0 ↔ v = 0 := by
  constructor
  · intro hWeight
    have hOperatorWeight :
        NQubitPauliOperator.weight
          (binarySymplecticVectorToOperator v) = 0 := by
      simpa using hWeight
    have hOperatorIdentity :=
      (NQubitPauliOperator.weight_eq_zero_iff
        (binarySymplecticVectorToOperator v)).mp hOperatorWeight
    have hSymplectic := congrArg NQubitPauliOperator.toSymplectic hOperatorIdentity
    calc
      v = NQubitPauliOperator.toSymplectic
          (NQubitPauliOperator.identity n) := by simpa using hSymplectic
      _ = 0 := by
        change NQubitPauliOperator.toSymplectic
          (1 : NQubitPauliGroupElement n).operators = 0
        exact Quantum.toSymplectic_one_operators
  · rintro rfl
    simp [symplecticWeight, symplecticSupport]

theorem binarySymplecticVectorToOperator_baseEmbedding
    {n c : ℕ} (v : BinarySymplecticVector n) :
    binarySymplecticVectorToOperator (baseSymplecticEmbedding n c v) =
      (binarySymplecticVectorToOperator v).appendIdentity c := by
  ext q
  refine Fin.addCases (fun i => ?_) (fun i => ?_) q
  · simp [binarySymplecticVectorToOperator,
      NQubitPauliOperator.appendIdentity]
  · simp [binarySymplecticVectorToOperator,
      NQubitPauliOperator.appendIdentity]

theorem binarySymplecticVectorToPauli_baseEmbedding
    {n c : ℕ} (v : BinarySymplecticVector n) :
    binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) =
      NQubitPauliGroupElement.ofOperator
        ((binarySymplecticVectorToOperator v).appendIdentity c) := by
  apply NQubitPauliGroupElement.ext
  · rfl
  · exact binarySymplecticVectorToOperator_baseEmbedding v

theorem binarySymplecticVectorToPauli_baseEmbedding_toSymplectic
    {n c : ℕ} (op : NQubitPauliOperator n) :
    binarySymplecticVectorToPauli
        (baseSymplecticEmbedding n c
          (NQubitPauliOperator.toSymplectic op)) =
      NQubitPauliGroupElement.ofOperator (op.appendIdentity c) := by
  rw [binarySymplecticVectorToPauli_baseEmbedding,
    binarySymplecticVectorToOperator_toSymplectic_inverse]

@[simp]
theorem symplecticWeight_baseEmbedding
    {n c : ℕ} (v : BinarySymplecticVector n) :
    symplecticWeight (baseSymplecticEmbedding n c v) =
      symplecticWeight v := by
  rw [← binarySymplecticVectorToOperator_weight,
    binarySymplecticVectorToOperator_baseEmbedding,
    NQubitPauliOperator.weight_appendIdentity,
    binarySymplecticVectorToOperator_weight]

/-- 根空间等子空间之外的最小辛重量。要求 V 中不属于 W 的向量重量均不小于 d，
并存在达到 d 的向量，且 d 为正数。若该差集为空，条件不成立。
以下证明非空差集上最小重量的存在性与唯一性。
-/
def HasMinimumSymplecticWeightOutside
    {n : ℕ} (V W : BinarySymplecticSubspace n) (d : ℕ) : Prop :=
  1 ≤ d ∧
    (∀ v : BinarySymplecticVector n,
      v ∈ V → v ∉ W → d ≤ symplecticWeight v) ∧
    (∃ v : BinarySymplecticVector n,
      v ∈ V ∧ v ∉ W ∧ symplecticWeight v = d)

theorem exists_hasMinimumSymplecticWeightOutside
    {n : ℕ} (V W : BinarySymplecticSubspace n)
    (hNonempty : ∃ v : BinarySymplecticVector n, v ∈ V ∧ v ∉ W) :
    ∃ d : ℕ, HasMinimumSymplecticWeightOutside V W d := by
  classical
  let Attained : ℕ → Prop := fun d =>
    ∃ v : BinarySymplecticVector n,
      v ∈ V ∧ v ∉ W ∧ symplecticWeight v = d
  have hAttained : ∃ d : ℕ, Attained d := by
    obtain ⟨v, hvV, hvW⟩ := hNonempty
    exact ⟨symplecticWeight v, v, hvV, hvW, rfl⟩
  let d := Nat.find hAttained
  obtain ⟨v, hvV, hvW, hWeight⟩ := Nat.find_spec hAttained
  have hdPos : 1 ≤ d := by
    change 1 ≤ Nat.find hAttained
    rw [← hWeight]
    apply Nat.one_le_iff_ne_zero.mpr
    intro hZero
    have hvZero := (symplecticWeight_eq_zero_iff v).mp hZero
    subst v
    exact hvW W.zero_mem
  have hLower : ∀ w : BinarySymplecticVector n,
      w ∈ V → w ∉ W → d ≤ symplecticWeight w := by
    intro w hwV hwW
    exact Nat.find_min' hAttained ⟨w, hwV, hwW, rfl⟩
  exact ⟨d, hdPos, hLower, ⟨v, hvV, hvW, hWeight⟩⟩

theorem HasMinimumSymplecticWeightOutside.unique
    {n d d' : ℕ} {V W : BinarySymplecticSubspace n}
    (h : HasMinimumSymplecticWeightOutside V W d)
    (h' : HasMinimumSymplecticWeightOutside V W d') :
    d = d' := by
  obtain ⟨v, hvV, hvW, hWeight⟩ := h.2.2
  obtain ⟨v', hvV', hvW', hWeight'⟩ := h'.2.2
  apply Nat.le_antisymm
  · simpa [hWeight'] using h.2.1 v' hvV' hvW'
  · simpa [hWeight] using h'.2.1 v hvV hvW

namespace StabilizerGroup.StabilizerCode

/- 由非平凡逻辑算子与子空间差集的对应，将发送端距离条件转化为最小辛重量条件。
-/
theorem hasBaseDistance_iff_hasMinimumSymplecticWeightOutside_of_logical_iff
    {n c k d : ℕ}
    (Q : StabilizerGroup.StabilizerCode (n + c) k)
    (V W : BinarySymplecticSubspace n)
    (hLogical : ∀ op : NQubitPauliOperator n,
      StabilizerGroup.IsNontrivialLogicalOperator
          (NQubitPauliGroupElement.ofOperator (op.appendIdentity c))
          Q.toStabilizerGroup ↔
        NQubitPauliOperator.toSymplectic op ∈ V ∧
          NQubitPauliOperator.toSymplectic op ∉ W) :
    Q.HasBaseDistance (n := n) (c := c) d ↔
      HasMinimumSymplecticWeightOutside V W d := by
  constructor
  · rintro ⟨hd, hLower, hWitness⟩
    refine ⟨hd, ?_, ?_⟩
    · intro v hvV hvW
      let op := binarySymplecticVectorToOperator v
      have hOpLogical :
          StabilizerGroup.IsNontrivialLogicalOperator
            (NQubitPauliGroupElement.ofOperator (op.appendIdentity c))
            Q.toStabilizerGroup := by
        apply (hLogical op).mpr
        simpa [op] using And.intro hvV hvW
      have hBound := hLower op hOpLogical
      simpa [op] using hBound
    · obtain ⟨op, hOpLogical, hWeight⟩ := hWitness
      let v := NQubitPauliOperator.toSymplectic op
      have hv := (hLogical op).mp hOpLogical
      refine ⟨v, hv.1, hv.2, ?_⟩
      exact (symplecticWeight_toSymplectic op).trans hWeight
  · rintro ⟨hd, hLower, hWitness⟩
    refine ⟨hd, ?_, ?_⟩
    · intro op hOpLogical
      have hv := (hLogical op).mp hOpLogical
      have hBound := hLower
        (NQubitPauliOperator.toSymplectic op) hv.1 hv.2
      simpa [symplecticWeight_toSymplectic] using hBound
    · obtain ⟨v, hvV, hvW, hWeight⟩ := hWitness
      let op := binarySymplecticVectorToOperator v
      refine ⟨op, ?_, ?_⟩
      · apply (hLogical op).mpr
        simpa [op] using And.intro hvV hvW
      · simpa [op] using hWeight

end StabilizerGroup.StabilizerCode

namespace EASymplecticData

/- 发送端算子与稳定子元素仅相差整体相位，当且仅当其辛向量属于根空间。
以下据此证明原码的非平凡逻辑算子对应辛对偶 S⊥ 中除去 R(S) 的部分，
对偶码则对应原空间 S 中除去 R(S) 的部分。
-/
theorem exists_stabilizer_sameOperator_as_basePauli_iff_mem_radical
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (v : BinarySymplecticVector n) :
    (∃ s ∈ A.toStabilizerCode.toStabilizerGroup.toSubgroup,
        s.operators =
          (binarySymplecticVectorToPauli
            (baseSymplecticEmbedding n c v)).operators) ↔
      v ∈ symplecticRadical A.stabilizerSpace := by
  let T := A.chosenRadicalDecomposition.extendedStabilizerSpace A.hasType
  have hRealizes :=
    A.chosenRadicalDecomposition.extendedStabilizerSpace_realizesEAStabilizerSpace
      A.hasType
  constructor
  · rintro ⟨s, hs, hOperators⟩
    rw [A.toStabilizerCode_toStabilizerGroup] at hs
    change s ∈ Subgroup.closure
      (NQubitPauliGroupElement.listToSet T.pauliGeneratorsList) at hs
    have hsSpan :=
      NQubitPauliGroupElement.mem_closure_implies_symp_in_span
        T.pauliGeneratorsList T.pauliGeneratorsList_phaseZero s hs
    rw [T.pauliGeneratorsList_sympSpan_eq] at hsSpan
    have hEmbedded : baseSymplecticEmbedding n c v ∈ T := by
      simpa [hOperators] using hsSpan
    have hBaseOnly : v ∈ T.baseOnlySpace :=
      (BinarySymplecticSubspace.mem_baseOnlySpace_iff T v).mpr hEmbedded
    rw [hRealizes.2.2.2] at hBaseOnly
    exact hBaseOnly
  · intro hv
    have hBaseOnly : v ∈ T.baseOnlySpace := by
      rw [hRealizes.2.2.2]
      exact hv
    have hEmbedded : baseSymplecticEmbedding n c v ∈ T :=
      (BinarySymplecticSubspace.mem_baseOnlySpace_iff T v).mp hBaseOnly
    have hSpan :
        NQubitPauliOperator.toSymplectic
            (binarySymplecticVectorToPauli
              (baseSymplecticEmbedding n c v)).operators ∈
          NQubitPauliGroupElement.sympSpan T.pauliGeneratorsList := by
      rw [binarySymplecticVectorToPauli_toSymplectic,
        T.pauliGeneratorsList_sympSpan_eq]
      exact hEmbedded
    obtain ⟨s, hs, hOperators⟩ :=
      NQubitPauliGroupElement.exists_mem_closure_of_symp_in_span
        T.pauliGeneratorsList
        (binarySymplecticVectorToPauli
          (baseSymplecticEmbedding n c v)).operators hSpan
    refine ⟨s, ?_, hOperators⟩
    rw [A.toStabilizerCode_toStabilizerGroup]
    change s ∈ Subgroup.closure
      (NQubitPauliGroupElement.listToSet T.pauliGeneratorsList)
    exact hs

theorem basePauli_isNontrivialLogicalOperator_iff
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (v : BinarySymplecticVector n) :
    StabilizerGroup.IsNontrivialLogicalOperator
        (binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v))
        A.toStabilizerCode.toStabilizerGroup ↔
      v ∈ NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace ∧
        v ∉ symplecticRadical A.stabilizerSpace := by
  rw [StabilizerGroup.IsNontrivialLogicalOperator_iff]
  constructor
  · intro hLogical
    have hNormalizer :
        binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) ∈
          StabilizerGroup.pauliNormalizer
            A.toStabilizerCode.toStabilizerGroup := by
      rw [StabilizerGroup.pauliNormalizer_eq_centralizer]
      exact hLogical.1
    have hDual :=
      (A.basePauli_mem_toStabilizerCode_pauliNormalizer_iff v).mp hNormalizer
    refine ⟨hDual, ?_⟩
    intro hRadical
    obtain ⟨s, hs, hOperators⟩ :=
      (A.exists_stabilizer_sameOperator_as_basePauli_iff_mem_radical v).mpr
        hRadical
    exact hLogical.2.2 s hs hOperators
  · rintro ⟨hDual, hNotRadical⟩
    have hCentralizer :
        binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) ∈
          StabilizerGroup.centralizer A.toStabilizerCode.toStabilizerGroup := by
      rw [← StabilizerGroup.pauliNormalizer_eq_centralizer]
      exact (A.basePauli_mem_toStabilizerCode_pauliNormalizer_iff v).mpr hDual
    have hNoSameOperator :
        ∀ s ∈ A.toStabilizerCode.toStabilizerGroup.toSubgroup,
          s.operators ≠
            (binarySymplecticVectorToPauli
              (baseSymplecticEmbedding n c v)).operators := by
      intro s hs hOperators
      exact hNotRadical
        ((A.exists_stabilizer_sameOperator_as_basePauli_iff_mem_radical v).mp
          ⟨s, hs, hOperators⟩)
    have hNotMem :
        binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) ∉
          A.toStabilizerCode.toStabilizerGroup.toSubgroup := by
      intro hMem
      exact hNoSameOperator
        (binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v))
        hMem rfl
    exact ⟨hCentralizer, hNotMem, hNoSameOperator⟩

theorem baseOperator_isNontrivialLogicalOperator_iff
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (op : NQubitPauliOperator n) :
    StabilizerGroup.IsNontrivialLogicalOperator
        (NQubitPauliGroupElement.ofOperator (op.appendIdentity c))
        A.toStabilizerCode.toStabilizerGroup ↔
      NQubitPauliOperator.toSymplectic op ∈
          NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace ∧
        NQubitPauliOperator.toSymplectic op ∉
          symplecticRadical A.stabilizerSpace := by
  rw [← binarySymplecticVectorToPauli_baseEmbedding_toSymplectic]
  exact A.basePauli_isNontrivialLogicalOperator_iff
    (NQubitPauliOperator.toSymplectic op)

theorem basePauli_isNontrivialLogicalOperator_toDualCode_iff
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (v : BinarySymplecticVector n) :
    StabilizerGroup.IsNontrivialLogicalOperator
        (binarySymplecticVectorToPauli (baseSymplecticEmbedding n k v))
        A.toDualStabilizerCode.toStabilizerGroup ↔
      v ∈ A.stabilizerSpace ∧
        v ∉ symplecticRadical A.stabilizerSpace := by
  change StabilizerGroup.IsNontrivialLogicalOperator
      (binarySymplecticVectorToPauli (baseSymplecticEmbedding n k v))
      A.symplecticDualData.toStabilizerCode.toStabilizerGroup ↔
    v ∈ A.stabilizerSpace ∧ v ∉ symplecticRadical A.stabilizerSpace
  have hLogical :=
    A.symplecticDualData.basePauli_isNontrivialLogicalOperator_iff v
  refine hLogical.trans ?_
  simp only [symplecticDualData_stabilizerSpace,
    BinarySymplecticSubspace.sympOrthogonal_sympOrthogonal,
    BinarySymplecticSubspace.radical_sympOrthogonal]

theorem baseOperator_isNontrivialLogicalOperator_toDualCode_iff
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (op : NQubitPauliOperator n) :
    StabilizerGroup.IsNontrivialLogicalOperator
        (NQubitPauliGroupElement.ofOperator (op.appendIdentity k))
        A.toDualStabilizerCode.toStabilizerGroup ↔
      NQubitPauliOperator.toSymplectic op ∈ A.stabilizerSpace ∧
        NQubitPauliOperator.toSymplectic op ∉
          symplecticRadical A.stabilizerSpace := by
  rw [← binarySymplecticVectorToPauli_baseEmbedding_toSymplectic]
  exact A.basePauli_isNontrivialLogicalOperator_toDualCode_iff
    (NQubitPauliOperator.toSymplectic op)

/-- 完整二元辛空间纠缠辅助码对偶定理。汇总原码与对偶码的参数、扩展稳定子空间的实现条件，
以及发送端正规化子分别对应 S⊥ 和 S 的关系。
原码在 k > 0 时具有 S⊥ ∖ R(S) 上的最小辛重量距离；
对偶码在 c > 0 时具有 S ∖ R(S) 上的最小辛重量距离。
-/
theorem symplecticEAQECCDuality_full
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    (
      k = n + c - m ∧
      k = n - c - l ∧
      (0 < k →
        ∃ d : ℕ,
          StabilizerGroup.StabilizerCode.HasBaseDistance
              (n := n) (c := c) A.toStabilizerCode d ∧
            HasMinimumSymplecticWeightOutside
              (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace)
              (symplecticRadical A.stabilizerSpace) d) ∧
      RealizesEAStabilizerSpace
        (NQubitPauliGroupElement.sympSpan
          A.toStabilizerCode.generatorsList)
        A.stabilizerSpace ∧
      {v : BinarySymplecticVector n |
        binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) ∈
          StabilizerGroup.pauliNormalizer
            A.toStabilizerCode.toStabilizerGroup} =
        (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace :
          Set (BinarySymplecticVector n))
    ) ∧
    (
      (0 < c →
        ∃ d' : ℕ,
          StabilizerGroup.StabilizerCode.HasBaseDistance
              (n := n) (c := k) A.toDualStabilizerCode d' ∧
            HasMinimumSymplecticWeightOutside A.stabilizerSpace
              (symplecticRadical A.stabilizerSpace) d') ∧
      RealizesEAStabilizerSpace
        (NQubitPauliGroupElement.sympSpan
          A.toDualStabilizerCode.generatorsList)
        (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace) ∧
      {v : BinarySymplecticVector n |
        binarySymplecticVectorToPauli (baseSymplecticEmbedding n k v) ∈
          StabilizerGroup.pauliNormalizer
            A.toDualStabilizerCode.toStabilizerGroup} =
        (A.stabilizerSpace : Set (BinarySymplecticVector n))
    ) := by

  have hParameter : k = n + c - m := A.parameter_eq
  have hDimensionAccounting :=
    A.radicalFinrank_add_ebitCount_add_logicalDimension_eq_length
  have hAlternativeParameter : k = n - c - l := by
    omega

  have hOriginalDistanceIff :
      ∀ d : ℕ,
        StabilizerGroup.StabilizerCode.HasBaseDistance
            (n := n) (c := c) A.toStabilizerCode d ↔
          HasMinimumSymplecticWeightOutside
            (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace)
            (symplecticRadical A.stabilizerSpace) d := by
    intro d
    exact
      StabilizerGroup.StabilizerCode.hasBaseDistance_iff_hasMinimumSymplecticWeightOutside_of_logical_iff
        A.toStabilizerCode
        (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace)
        (symplecticRadical A.stabilizerSpace)
        A.baseOperator_isNontrivialLogicalOperator_iff
  have hDualDistanceIff :
      ∀ d' : ℕ,
        StabilizerGroup.StabilizerCode.HasBaseDistance
            (n := n) (c := k) A.toDualStabilizerCode d' ↔
          HasMinimumSymplecticWeightOutside A.stabilizerSpace
            (symplecticRadical A.stabilizerSpace) d' := by
    intro d'
    exact
      StabilizerGroup.StabilizerCode.hasBaseDistance_iff_hasMinimumSymplecticWeightOutside_of_logical_iff
        A.toDualStabilizerCode A.stabilizerSpace
        (symplecticRadical A.stabilizerSpace)
        A.baseOperator_isNontrivialLogicalOperator_toDualCode_iff

  have hOriginalDistanceExists :
      0 < k →
        ∃ d : ℕ,
          StabilizerGroup.StabilizerCode.HasBaseDistance
              (n := n) (c := c) A.toStabilizerCode d ∧
            HasMinimumSymplecticWeightOutside
              (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace)
              (symplecticRadical A.stabilizerSpace) d := by
    intro hk
    have hDomainNonempty :
        ∃ v : BinarySymplecticVector n,
          v ∈ NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace ∧
            v ∉ symplecticRadical A.stabilizerSpace := by
      by_contra hEmpty
      have hDualLeRadical :
          NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace ≤
            symplecticRadical A.stabilizerSpace := by
        intro v hvDual
        by_contra hvRadical
        exact hEmpty ⟨v, hvDual, hvRadical⟩
      have hFinrankLe := Submodule.finrank_mono hDualLeRadical
      have hDualDimension := A.symplecticDualData.hasType.1
      rw [A.symplecticDualData_stabilizerSpace] at hDualDimension
      have hDualAccounting :=
        A.symplecticDualData.radicalFinrank_add_two_mul_ebitCount_eq_stabilizerDimension
      rw [hDualDimension, A.radical_finrank] at hFinrankLe
      omega
    obtain ⟨d, hMinimum⟩ :=
      exists_hasMinimumSymplecticWeightOutside
        (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace)
        (symplecticRadical A.stabilizerSpace) hDomainNonempty
    exact ⟨d, (hOriginalDistanceIff d).mpr hMinimum, hMinimum⟩

  have hDualDistanceExists :
      0 < c →
        ∃ d' : ℕ,
          StabilizerGroup.StabilizerCode.HasBaseDistance
              (n := n) (c := k) A.toDualStabilizerCode d' ∧
            HasMinimumSymplecticWeightOutside A.stabilizerSpace
              (symplecticRadical A.stabilizerSpace) d' := by
    intro hc
    have hDomainNonempty :
        ∃ v : BinarySymplecticVector n,
          v ∈ A.stabilizerSpace ∧
            v ∉ symplecticRadical A.stabilizerSpace := by
      by_contra hEmpty
      have hStabilizerLeRadical :
          A.stabilizerSpace ≤ symplecticRadical A.stabilizerSpace := by
        intro v hvStabilizer
        by_contra hvRadical
        exact hEmpty ⟨v, hvStabilizer, hvRadical⟩
      have hFinrankLe := Submodule.finrank_mono hStabilizerLeRadical
      have hTypeAccounting :=
        A.radicalFinrank_add_two_mul_ebitCount_eq_stabilizerDimension
      rw [A.hasType.1, A.radical_finrank] at hFinrankLe
      omega
    obtain ⟨d', hMinimum⟩ :=
      exists_hasMinimumSymplecticWeightOutside A.stabilizerSpace
        (symplecticRadical A.stabilizerSpace) hDomainNonempty
    exact ⟨d', (hDualDistanceIff d').mpr hMinimum, hMinimum⟩

  have hOriginalRealizes :
      RealizesEAStabilizerSpace
        (NQubitPauliGroupElement.sympSpan
          A.toStabilizerCode.generatorsList)
        A.stabilizerSpace := by
    rw [A.toStabilizerCode_generators_sympSpan_eq_extendedStabilizerSpace]
    exact ⟨
      A.chosenRadicalDecomposition.extendedStabilizerSpace_isTotallyIsotropic
        A.hasType,
      A.chosenRadicalDecomposition.extendedStabilizerSpace_inf_projectionKer_eq_bot
        A.hasType,
      A.chosenRadicalDecomposition.extendedStabilizerSpace_projectedSpace_eq
        A.hasType,
      A.chosenRadicalDecomposition.extendedStabilizerSpace_baseOnlySpace_eq_radical
        A.hasType⟩

  have hDualRealizes :
      RealizesEAStabilizerSpace
        (NQubitPauliGroupElement.sympSpan
          A.toDualStabilizerCode.generatorsList)
        (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace) := by
    change RealizesEAStabilizerSpace
      (NQubitPauliGroupElement.sympSpan
        A.symplecticDualData.toStabilizerCode.generatorsList)
      (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace)
    rw [A.symplecticDualData.toStabilizerCode_generators_sympSpan_eq_extendedStabilizerSpace]
    have hRealization :
        RealizesEAStabilizerSpace
          (A.symplecticDualData.chosenRadicalDecomposition.extendedStabilizerSpace
            A.symplecticDualData.hasType)
          A.symplecticDualData.stabilizerSpace := ⟨
      A.symplecticDualData.chosenRadicalDecomposition.extendedStabilizerSpace_isTotallyIsotropic
        A.symplecticDualData.hasType,
      A.symplecticDualData.chosenRadicalDecomposition.extendedStabilizerSpace_inf_projectionKer_eq_bot
        A.symplecticDualData.hasType,
      A.symplecticDualData.chosenRadicalDecomposition.extendedStabilizerSpace_projectedSpace_eq
        A.symplecticDualData.hasType,
      A.symplecticDualData.chosenRadicalDecomposition.extendedStabilizerSpace_baseOnlySpace_eq_radical
        A.symplecticDualData.hasType⟩
    simpa only [A.symplecticDualData_stabilizerSpace] using hRealization

  have hOriginalNormalizer :
      {v : BinarySymplecticVector n |
        binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) ∈
          StabilizerGroup.pauliNormalizer
            A.toStabilizerCode.toStabilizerGroup} =
        (NQubitPauliGroupElement.sympOrthogonal A.stabilizerSpace :
          Set (BinarySymplecticVector n)) := by
    ext v
    exact A.basePauli_mem_toStabilizerCode_pauliNormalizer_iff v
  have hDualNormalizer :
      {v : BinarySymplecticVector n |
        binarySymplecticVectorToPauli (baseSymplecticEmbedding n k v) ∈
          StabilizerGroup.pauliNormalizer
            A.toDualStabilizerCode.toStabilizerGroup} =
        (A.stabilizerSpace : Set (BinarySymplecticVector n)) := by
    ext v
    exact A.basePauli_mem_toDualStabilizerCode_pauliNormalizer_iff v

  exact ⟨
    ⟨hParameter, hAlternativeParameter, hOriginalDistanceExists,
      hOriginalRealizes, hOriginalNormalizer⟩,
    ⟨hDualDistanceExists, hDualRealizes, hDualNormalizer⟩⟩

end EASymplecticData

end Quantum
