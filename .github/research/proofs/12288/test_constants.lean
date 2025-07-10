import PrimeOS12288.Constants.All

-- Test that we can access all constants
#check PrimeOS12288.Constants.α₀
#check PrimeOS12288.Constants.α₁
#check PrimeOS12288.Constants.α₂
#check PrimeOS12288.Constants.α₃
#check PrimeOS12288.Constants.α₄
#check PrimeOS12288.Constants.α₅
#check PrimeOS12288.Constants.α₆
#check PrimeOS12288.Constants.α₇

-- Test the fieldConstant function
#check PrimeOS12288.Constants.fieldConstant
#check PrimeOS12288.Constants.all_positive
#check PrimeOS12288.Constants.all_nonzero

-- Test that α₆ and α₇ come from the axiom
#check PrimeOS12288.Constants.α₆_α₇_spec