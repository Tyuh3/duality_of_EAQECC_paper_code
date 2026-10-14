import EAQECC.Quaternary.Distance
import EAQECC.Symplectic.EACode

/-!
四元加性码的纠缠辅助码对偶理论。把四元输入转换为二元辛输入，
复用二元构造，再用对偶、根空间及重量保持关系返回四元表述。
-/

namespace Quantum
namespace Quaternary

/- 用四元加性码表示扩展稳定子空间的实现条件与发送端正规化子。
后续引理把二元正规化子的空间对应转换为四元对应。
-/
def IsAdditiveEAStabilizerOf
    {n e k : ℕ} (C : QuaternaryAdditiveCode n)
    (Q : StabilizerGroup.StabilizerCode (n + e) k) : Prop :=
  RealizesEAStabilizerSpace
    (NQubitPauliGroupElement.sympSpan Q.generatorsList)
    (quaternaryToBinarySubspace C)

def IsAdditiveEANormalizerOf
    {n e k : ℕ} (N : QuaternaryAdditiveCode n)
    (Q : StabilizerGroup.StabilizerCode (n + e) k) : Prop :=
  {u : QuaternaryVector n |
      binarySymplecticVectorToPauli
          (baseSymplecticEmbedding n e (quaternaryToBinary n u)) ∈
        StabilizerGroup.pauliNormalizer Q.toStabilizerGroup} =
    (N : Set (QuaternaryVector n))

theorem isAdditiveEANormalizerOf_of_binaryNormalizer
    {n e k : ℕ} (N : QuaternaryAdditiveCode n)
    (Q : StabilizerGroup.StabilizerCode (n + e) k)
    (hNormalizer :
      {v : BinarySymplecticVector n |
          binarySymplecticVectorToPauli (baseSymplecticEmbedding n e v) ∈
            StabilizerGroup.pauliNormalizer Q.toStabilizerGroup} =
        ((quaternaryToBinarySubspace N : BinarySymplecticSubspace n) :
          Set (BinarySymplecticVector n))) :
    IsAdditiveEANormalizerOf N Q := by
  unfold IsAdditiveEANormalizerOf
  ext u
  have hu := Set.ext_iff.mp hNormalizer (quaternaryToBinary n u)
  simpa using hu

/-- 四元加性码输入数据。保存加性码 C、迹类型 [m,c]ₜ、迹根空间的二元维数 l，
以及输入参数关系 k = n + c − m。这里的维数均按二元域计算。
码构造及距离关系通过转换到二元辛输入后证明。
-/
structure EAAdditiveCodeData (n m l c k : ℕ) where
  additiveCode : QuaternaryAdditiveCode n
  hasTraceType : additiveCode.HasTraceType m c
  radical_finrank :
    Module.finrank (ZMod 2) (traceRadical additiveCode) = l
  parameter_eq : k = n + c - m

namespace EAAdditiveCodeData

/- 将加性码转换为二元辛输入，保持类型、根空间维数与参数。
随后分别调用二元构造得到原码和对偶码的扩展稳定子码。
-/
noncomputable def toEASymplecticData
    {n m l c k : ℕ} (D : EAAdditiveCodeData n m l c k) :
    EASymplecticData n m l c k :=
  { stabilizerSpace := quaternaryToBinarySubspace D.additiveCode
    hasType :=
      QuaternaryAdditiveCode.hasTraceType_iff_preimage_hasType.mp
        D.hasTraceType
    radical_finrank := by
      rw [← quaternaryToBinarySubspace_traceRadical D.additiveCode,
        finrank_quaternaryToBinarySubspace]
      exact D.radical_finrank
    parameter_eq := D.parameter_eq }

noncomputable def toStabilizerCode
    {n m l c k : ℕ} (D : EAAdditiveCodeData n m l c k) :
    StabilizerGroup.StabilizerCode (n + c) k :=
  D.toEASymplecticData.toStabilizerCode

noncomputable def toDualStabilizerCode
    {n m l c k : ℕ} (D : EAAdditiveCodeData n m l c k) :
    StabilizerGroup.StabilizerCode (n + k) c :=
  D.toEASymplecticData.toDualStabilizerCode

/-- 完整四元加性码纠缠辅助码对偶定理。给出参数关系与迹对偶类型，
并证明两侧扩展稳定子空间及发送端正规化子的四元对应。
原码在 k > 0 时的距离为 C⊥ ∖ R(C) 上的最小汉明重量；
对偶码在 c > 0 时的距离为 C ∖ R(C) 上的最小汉明重量。
-/
theorem quaternaryEAQECCDuality_full
    {n m l c k : ℕ} (D : EAAdditiveCodeData n m l c k) :
    (
      k = n + c - m ∧
      k = n - c - l ∧
      (0 < k →
        ∃ d : ℕ,
          StabilizerGroup.StabilizerCode.HasBaseDistance
              (n := n) (c := c) D.toStabilizerCode d ∧
            HasMinimumHammingWeightOutside
              (traceOrthogonal D.additiveCode)
              (traceRadical D.additiveCode) d) ∧
      IsAdditiveEAStabilizerOf D.additiveCode D.toStabilizerCode ∧
      IsAdditiveEANormalizerOf
        (traceOrthogonal D.additiveCode) D.toStabilizerCode
    ) ∧
    (
      (traceOrthogonal D.additiveCode).HasTraceType
        (2 * n - m) (n + c - m) ∧
      (0 < c →
        ∃ d' : ℕ,
          StabilizerGroup.StabilizerCode.HasBaseDistance
              (n := n) (c := k)
              D.toDualStabilizerCode d' ∧
            HasMinimumHammingWeightOutside D.additiveCode
              (traceRadical D.additiveCode) d') ∧
      IsAdditiveEAStabilizerOf
        (traceOrthogonal D.additiveCode) D.toDualStabilizerCode ∧
      IsAdditiveEANormalizerOf D.additiveCode D.toDualStabilizerCode
    ) := by
  have hSymplecticDuality :=
    D.toEASymplecticData.symplecticEAQECCDuality_full
  rcases hSymplecticDuality with
    ⟨⟨hParameter, hAlternativeParameter, hOriginalDistance,
        hOriginalRealizes, hOriginalNormalizer⟩,
      ⟨hDualDistance, hDualRealizes, hDualNormalizer⟩⟩

  have hOriginalDistanceQuaternary :
      0 < k →
        ∃ d : ℕ,
          StabilizerGroup.StabilizerCode.HasBaseDistance
              (n := n) (c := c) D.toStabilizerCode d ∧
            HasMinimumHammingWeightOutside
              (traceOrthogonal D.additiveCode)
              (traceRadical D.additiveCode) d := by
    intro hk
    obtain ⟨d, hCodeDistance, hMinimumBinary⟩ := hOriginalDistance hk
    refine ⟨d, ?_, ?_⟩
    · simpa [toStabilizerCode] using hCodeDistance
    · apply
        (hasMinimumHammingWeight_traceOrthogonal_diff_traceRadical_iff
          D.additiveCode).mpr
      simpa [toEASymplecticData] using hMinimumBinary

  have hDualDistanceQuaternary :
      0 < c →
        ∃ d' : ℕ,
          StabilizerGroup.StabilizerCode.HasBaseDistance
              (n := n) (c := k)
              D.toDualStabilizerCode d' ∧
            HasMinimumHammingWeightOutside D.additiveCode
              (traceRadical D.additiveCode) d' := by
    intro hc
    obtain ⟨d', hCodeDistance, hMinimumBinary⟩ := hDualDistance hc
    refine ⟨d', ?_, ?_⟩
    · simpa [toDualStabilizerCode] using hCodeDistance
    · apply
        (hasMinimumHammingWeight_code_diff_traceRadical_iff
          D.additiveCode).mpr
      simpa [toEASymplecticData] using hMinimumBinary

  have hOriginalStabilizer :
      IsAdditiveEAStabilizerOf D.additiveCode D.toStabilizerCode := by
    simpa [IsAdditiveEAStabilizerOf, toStabilizerCode,
      toEASymplecticData] using hOriginalRealizes

  have hOriginalNormalizerBinary :
      {v : BinarySymplecticVector n |
          binarySymplecticVectorToPauli (baseSymplecticEmbedding n c v) ∈
            StabilizerGroup.pauliNormalizer
              D.toStabilizerCode.toStabilizerGroup} =
        ((quaternaryToBinarySubspace
            (traceOrthogonal D.additiveCode) : BinarySymplecticSubspace n) :
          Set (BinarySymplecticVector n)) := by
    rw [quaternaryToBinarySubspace_traceOrthogonal]
    simpa [toStabilizerCode, toEASymplecticData] using hOriginalNormalizer
  have hOriginalNormalizerQuaternary :
      IsAdditiveEANormalizerOf
        (traceOrthogonal D.additiveCode) D.toStabilizerCode :=
    isAdditiveEANormalizerOf_of_binaryNormalizer
      (traceOrthogonal D.additiveCode) D.toStabilizerCode
      hOriginalNormalizerBinary

  have hDualStabilizer :
      IsAdditiveEAStabilizerOf
        (traceOrthogonal D.additiveCode) D.toDualStabilizerCode := by
    unfold IsAdditiveEAStabilizerOf
    rw [quaternaryToBinarySubspace_traceOrthogonal]
    simpa [toDualStabilizerCode, toEASymplecticData] using hDualRealizes

  have hDualNormalizerBinary :
      {v : BinarySymplecticVector n |
          binarySymplecticVectorToPauli
              (baseSymplecticEmbedding n k v) ∈
            StabilizerGroup.pauliNormalizer
              D.toDualStabilizerCode.toStabilizerGroup} =
        ((quaternaryToBinarySubspace D.additiveCode :
            BinarySymplecticSubspace n) : Set (BinarySymplecticVector n)) := by
    simpa [toDualStabilizerCode, toEASymplecticData] using hDualNormalizer
  have hDualNormalizerQuaternary :
      IsAdditiveEANormalizerOf D.additiveCode D.toDualStabilizerCode :=
    isAdditiveEANormalizerOf_of_binaryNormalizer
      D.additiveCode D.toDualStabilizerCode hDualNormalizerBinary

  have hDualType :
      (traceOrthogonal D.additiveCode).HasTraceType
        (2 * n - m) (n + c - m) :=
    QuaternaryAdditiveCode.traceOrthogonal_hasTraceType
      D.hasTraceType

  exact
    ⟨⟨hParameter, hAlternativeParameter, hOriginalDistanceQuaternary,
        hOriginalStabilizer, hOriginalNormalizerQuaternary⟩,
      ⟨hDualType, hDualDistanceQuaternary, hDualStabilizer,
        hDualNormalizerQuaternary⟩⟩

/-- 四元加性码对偶定理的参数与距离推论。
从完整定理提取参数关系、迹对偶类型和两侧距离，供纠缠辅助码模型调用。
稳定子空间与正规化子的对应仍由完整定理给出。
-/
theorem quaternaryEAQECCDuality
    {n m l c k : ℕ} (D : EAAdditiveCodeData n m l c k) :
    k = n + c - m ∧
    k = n - c - l ∧
    (0 < k →
      ∃ d : ℕ,
        D.toEASymplecticData.toEACode.HasDistance d ∧
          HasMinimumHammingWeightOutside
            (traceOrthogonal D.additiveCode)
            (traceRadical D.additiveCode) d) ∧
    (traceOrthogonal D.additiveCode).HasTraceType
      (2 * n - m) (n + c - m) ∧
    (0 < c →
      ∃ d' : ℕ,
        D.toEASymplecticData.symplecticDualData.toEACode.HasDistance d' ∧
          HasMinimumHammingWeightOutside D.additiveCode
            (traceRadical D.additiveCode) d') := by
  rcases D.quaternaryEAQECCDuality_full with
    ⟨⟨hParameter, hAlternativeParameter, hOriginalDistance, _, _⟩,
      ⟨hDualType, hDualDistance, _, _⟩⟩
  refine ⟨hParameter, hAlternativeParameter, ?_, hDualType, ?_⟩
  · intro hk
    obtain ⟨d, hDistance, hMinimum⟩ := hOriginalDistance hk
    exact ⟨d, hDistance, hMinimum⟩
  · intro hc
    obtain ⟨d', hDistance, hMinimum⟩ := hDualDistance hc
    exact ⟨d', hDistance, hMinimum⟩

end EAAdditiveCodeData

end Quaternary
end Quantum
