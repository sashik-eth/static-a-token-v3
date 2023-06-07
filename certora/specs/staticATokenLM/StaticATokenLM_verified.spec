import "../methods/methods_base.spec"

/////////////////// Methods ////////////////////////

////////////////// FUNCTIONS //////////////////////

///////////////// Properties ///////////////////////

methods {
    getRewardTokenFromReserveData() returns (address) envfree
    ecrecover(bytes32, uint8, bytes32, bytes32) returns (address) => ALWAYS(0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef)
}

ghost mathint sumUserBalances {
    init_state axiom sumUserBalances == 0;
}

hook Sstore balanceOf[KEY address user] uint256 newBalance
    (uint256 oldBalance) STORAGE {
        sumUserBalances = sumUserBalances + to_mathint(newBalance) - to_mathint(oldBalance);
}

hook Sload uint256 bal balanceOf[KEY address user] STORAGE {
    require sumUserBalances >= bal;
}
// Invariant to check that sum of all balances is equal to total supply
invariant userBalancesAreTotalSupply()
	to_mathint(totalSupply()) == sumUserBalances

// Checks that minted amount of shares is equal to preview function result
rule mintCorrectShares(env e, uint256 shares, address depositor) {
    uint256 previewMint = previewMint(e, shares);
    uint256 assets = mint(e, shares, depositor);
    assert previewMint == assets, "Minted wrong amount of shares";
}
// Checking that updating rewards during trasnfer result in correct amount of unclaimed rewards
rule updateRewards(env e, uint256 amount, address user, address rewardToken) {

    uint256 rewardsClaimable = getClaimableRewards(e, user, rewardToken);
    uint256 currentRewardsIndex = getCurrentRewardsIndex(e, rewardToken);

    updateUser(e, user, currentRewardsIndex, rewardToken);

    uint256 rewardsUnclaimed = getUnclaimedRewards(user, rewardToken);

    assert rewardsClaimable == rewardsUnclaimed, "Rewards were updated wrong during transfer";
}
// Check correct calculation of maxRedeemUnderliying amount
rule maxRedeemUnderliyingCalculation(env e, address user) {

    uint256 userBalance = balanceOf(user);
    
    address aTokenAddress = getRewardTokenFromReserveData();

    uint256 underlyingAmount = _DummyERC20_aTokenUnderlying.balanceOf(aTokenAddress);
    uint256 underlyingTokenBalanceInShares = convertToShares(e, underlyingAmount);

    uint256 expected = underlyingTokenBalanceInShares >= userBalance ? userBalance : underlyingTokenBalanceInShares;
    uint256 res = maxRedeemUnderlying(e, user);

    assert res > 0 => expected == res, "Wrong maxReedemUnderlying";
}
// Check convert to shares correct calculation
rule convertToSharesCorrect(env e, uint256 assets) {
    uint256 previewWithdraw = previewWithdraw(e, assets);
    uint256 previewDeposit = previewDeposit(e, assets);
    
    mathint rate = to_mathint(_SymbolicLendingPool.getReserveNormalizedIncome(e, _DummyERC20_aTokenUnderlying));
    mathint ray = to_mathint(RAY());
    require rate != 0;
    mathint calcWithdraw = (assets * ray + rate - 1) / rate;
    mathint calcDeposit = assets * ray / rate;

    assert to_mathint(previewWithdraw) == calcWithdraw && to_mathint(previewDeposit) == calcDeposit, "Wrong convertToShares calculation";
}
//  Check convert to asset correct calculation
rule convertToAssetsCorrect(env e, uint256 shares) {
    uint256 previewMint = previewMint(e, shares);
    uint256 previewRedeem = previewRedeem(e, shares);
    
    mathint rate = to_mathint(_SymbolicLendingPool.getReserveNormalizedIncome(e, _DummyERC20_aTokenUnderlying));
    mathint ray = to_mathint(RAY());
    require rate != 0;
    mathint calcMint = (shares * rate + ray - 1) / ray;
    mathint calcRedeem = shares * rate / ray;

    assert to_mathint(previewMint) == calcMint && to_mathint(previewRedeem) == calcRedeem, "Wrong convertToAssets calculation";
}
// Check pending rewards correct calculation
rule getPendingRewardsCorrect(env e, uint256 balance, uint256 rewardsIndexOnLastInteraction, uint256 currentRewardsIndex, uint256 assetUnit) {
    uint256 res = getPendingRewards(e, balance, rewardsIndexOnLastInteraction, currentRewardsIndex, assetUnit);
    require to_mathint(assetUnit) > 0;
    mathint calcRes = balance * (currentRewardsIndex - rewardsIndexOnLastInteraction) / assetUnit;
    assert calcRes == to_mathint(res), "Wrong getPendingRewardsCorrect calculation";
}
// Check that claimed rewards amount is correct
rule claimRewardsToSelf(env e) {
    require e.msg.sender != currentContract;
    address[] _rewards;
    require _rewards[0] == _DummyERC20_rewardToken;
    require _rewards.length == 1;
    
    uint256 _rewardsClaimable = getClaimableRewards(e, e.msg.sender, _DummyERC20_rewardToken);
    uint256 _balanceRew = _DummyERC20_rewardToken.balanceOf(e.msg.sender);

    claimRewardsToSelf(e, _rewards);

    uint256 rewardsClaimable_ = getClaimableRewards(e, e.msg.sender,  _DummyERC20_rewardToken);
    uint256 balanceRew_ = _DummyERC20_rewardToken.balanceOf(e.msg.sender);

    assert balanceRew_ - _balanceRew == _rewardsClaimable - rewardsClaimable_, "Rewards claim or update wrong";
}