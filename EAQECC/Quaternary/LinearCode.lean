import EAQECC.Quaternary.Duality
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.Dimension.Free

/-!
四元线性码作为四元加性码的特例。限制标量后复用加性码对偶理论。
-/

namespace Quantum
namespace Quaternary

/- 四元线性码及其加性码表示。以下证明限制到二元标量后码字不变、维数变为原来的两倍。
-/
abbrev QuaternaryLinearCode (n : ℕ) :=
  Submodule QuaternaryField (QuaternaryVector n)

namespace QuaternaryLinearCode

noncomputable def toAdditiveCode {n : ℕ}
    (C : QuaternaryLinearCode n) : QuaternaryAdditiveCode n :=
  C.restrictScalars (ZMod 2)

@[simp]
theorem mem_toAdditiveCode_iff {n : ℕ}
    (C : QuaternaryLinearCode n) (u : QuaternaryVector n) :
    u ∈ C.toAdditiveCode ↔ u ∈ C := by
  exact Submodule.restrictScalars_mem (ZMod 2) C u

@[simp]
theorem coe_toAdditiveCode {n : ℕ}
    (C : QuaternaryLinearCode n) :
    (C.toAdditiveCode : Set (QuaternaryVector n)) = C := by
  exact Submodule.coe_restrictScalars (ZMod 2) C

theorem finrank_toAdditiveCode {n : ℕ}
    (C : QuaternaryLinearCode n) :
    Module.finrank (ZMod 2) C.toAdditiveCode =
      2 * Module.finrank QuaternaryField C := by
  change Module.finrank (ZMod 2) (C.restrictScalars (ZMod 2)) =
    2 * Module.finrank QuaternaryField C
  calc
    Module.finrank (ZMod 2) (C.restrictScalars (ZMod 2)) =
        Module.finrank (ZMod 2) QuaternaryField *
          Module.finrank QuaternaryField (C.restrictScalars (ZMod 2)) :=
      (Module.finrank_mul_finrank
        (ZMod 2) QuaternaryField (C.restrictScalars (ZMod 2))).symm
    _ = 2 * Module.finrank QuaternaryField C := by
      rw [finrank_quaternaryField]
      exact congrArg (fun r : ℕ ↦ 2 * r)
        (C.restrictScalarsEquiv (ZMod 2)).finrank_eq

theorem finrank_toAdditiveCode_eq_two_mul
    {n k4 : ℕ} {C : QuaternaryLinearCode n}
    (hDimension : Module.finrank QuaternaryField C = k4) :
    Module.finrank (ZMod 2) C.toAdditiveCode = 2 * k4 := by
  rw [finrank_toAdditiveCode, hDimension]

/-- 四元线性码的纠缠辅助码对偶结论。
将线性码视为加性码后复用完整四元对偶定理，所得码参数与距离条件按二元维数计算。
-/
theorem eaqeccDuality_full
    {n k4 c : ℕ} (C : QuaternaryLinearCode n)
    (hDimension : Module.finrank QuaternaryField C = k4)
    (hType : C.toAdditiveCode.HasTraceType (2 * k4) c) :
    Module.finrank (ZMod 2) C.toAdditiveCode = 2 * k4 ∧
    (
      ∃ Q : StabilizerGroup.StabilizerCode
          (n + c) (n + c - 2 * k4),
        (0 < n + c - 2 * k4 →
          ∃ d : ℕ,
            StabilizerGroup.StabilizerCode.HasBaseDistance
                (n := n) (c := c) Q d ∧
              HasMinimumHammingWeightOutside
                (traceOrthogonal C.toAdditiveCode)
                (traceRadical C.toAdditiveCode) d) ∧
        IsAdditiveEAStabilizerOf C.toAdditiveCode Q ∧
        IsAdditiveEANormalizerOf
          (traceOrthogonal C.toAdditiveCode) Q
    ) ∧
    (
      (traceOrthogonal C.toAdditiveCode).HasTraceType
        (2 * n - 2 * k4) (n + c - 2 * k4) ∧
      ∃ Qperp : StabilizerGroup.StabilizerCode
          (n + (n + c - 2 * k4)) c,
        (0 < c →
          ∃ dperp : ℕ,
            StabilizerGroup.StabilizerCode.HasBaseDistance
                (n := n) (c := n + c - 2 * k4) Qperp dperp ∧
              HasMinimumHammingWeightOutside C.toAdditiveCode
                (traceRadical C.toAdditiveCode) dperp) ∧
        IsAdditiveEAStabilizerOf
          (traceOrthogonal C.toAdditiveCode) Qperp ∧
        IsAdditiveEANormalizerOf C.toAdditiveCode Qperp
    ) := by
  let l := Module.finrank (ZMod 2) (traceRadical C.toAdditiveCode)
  let D : EAAdditiveCodeData
      n (2 * k4) l c (n + c - 2 * k4) :=
    { additiveCode := C.toAdditiveCode
      hasTraceType := hType
      radical_finrank := rfl
      parameter_eq := rfl }
  have hQuaternaryDuality := D.quaternaryEAQECCDuality_full
  rcases hQuaternaryDuality with
    ⟨⟨_, _, hOriginalDistance, hOriginalStabilizer,
        hOriginalNormalizer⟩,
      ⟨hDualType, hDualDistance, hDualStabilizer,
        hDualNormalizer⟩⟩
  have hBinaryDimension := finrank_toAdditiveCode_eq_two_mul hDimension
  refine ⟨hBinaryDimension, ?_, ?_⟩
  · refine ⟨D.toStabilizerCode, ?_, ?_, ?_⟩
    · simpa [D] using hOriginalDistance
    · simpa [D] using hOriginalStabilizer
    · simpa [D] using hOriginalNormalizer
  · refine ⟨?_, D.toDualStabilizerCode, ?_, ?_, ?_⟩
    · simpa [D] using hDualType
    · simpa [D] using hDualDistance
    · simpa [D] using hDualStabilizer
    · simpa [D] using hDualNormalizer

end QuaternaryLinearCode

end Quaternary
end Quantum
