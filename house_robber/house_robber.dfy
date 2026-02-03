ghost function SumSet(S: set<nat>, nums: seq<int>): int
    requires forall i | i in S :: i < |nums|
    decreases |S|
{
    if S == {} then 0
    else
        var i: nat :| i in S;
        nums[i] + SumSet(S - {i}, nums)
}


ghost predicate money_extracted(value: int, nums: seq<int>) {
    exists S: set<nat> ::
        (forall i | i in S ::
            i < |nums|
            && !exists j | j in S :: (j == i + 1) || (j == i - 1))
        && SumSet(S, nums) == value
}

method houseRobber(nums: seq<int>) returns (result: int)
  ensures money_extracted(result, nums)
  ensures forall v :: money_extracted(v, nums) ==> v <= result
{
}