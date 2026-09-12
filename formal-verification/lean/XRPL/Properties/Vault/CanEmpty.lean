import XRPL.Properties.Vault.Common.CanEmptyProofs

/-! # Emptying a reachable `int64` vault -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A reachable `int64` vault within the `int64` cap can be emptied by a finite
withdrawal sequence. Restricted to `int64` because fractional one-share peeling
trips the sub-ULP precision-loss guard. `hcap`/`hAint` are the C++-guaranteed
representability rails that `Reachable` omits. -/
theorem Vault.Reachable.canEmpty (v : Vault) (hr : Vault.Reachable v)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hcap : v.assetsTotal.toRat ≤ 2 ^ 63 - 1)
    (hint : v.numericType = .int64)
    (hAint : v.assetsTotal.toRat.den = 1) : CanEmpty v :=
  Vault.Reachable.canEmpty_proof v hr hfit hcap hint hAint

end XRPL.Model.SingleAssetVault
