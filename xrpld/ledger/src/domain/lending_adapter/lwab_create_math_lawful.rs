pub(super) fn lawful(v: Vault) -> bool {
    let z = NumberParts::zero();
    let Ok(total) = raw(v.assets_total) else {
        return false;
    };
    let Ok(available) = raw(v.assets_available) else {
        return false;
    };
    let Ok(reserved) = raw(v.assets_reserved) else {
        return false;
    };
    let Ok(shares) = raw(v.shares_total) else {
        return false;
    };
    let Ok(loss) = raw(v.loss_unrealized) else {
        return false;
    };
    total >= z
        && available >= z
        && available <= total
        && shares >= z
        && loss >= z
        && loss <= total
        && (shares != z || (total == z && available == z))
        && reserved.is_normalized(MantissaScale::Large)
}
