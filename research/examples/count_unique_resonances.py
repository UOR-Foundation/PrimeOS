#!/usr/bin/env python3
"""
Count unique resonance values for all 256 bytes without quantization.
This script will determine the exact number of unique resonance values.
"""

import math
from fractions import Fraction
from decimal import Decimal, getcontext

# Set high precision for Decimal calculations
getcontext().prec = 50

# Field constants
PHI = (1 + math.sqrt(5)) / 2
PI = math.pi
E = math.e

def calculate_resonance(byte_value):
    """Calculate resonance for a single byte value."""
    # Scale to [0, 1]
    normalized = byte_value / 255.0
    
    # Field harmonics
    phi_harmonic = math.sin(normalized * PHI)
    pi_harmonic = math.cos(normalized * PI)
    e_harmonic = math.sin(normalized * E)
    
    # Resonance calculation
    resonance = (phi_harmonic + pi_harmonic + e_harmonic) / 3.0
    
    return resonance

def calculate_resonance_decimal(byte_value):
    """Calculate resonance using Decimal for higher precision."""
    # Convert constants to Decimal
    phi_decimal = Decimal('1.6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880753868917521266338622235369317931800607667263544333890865959395829056383226613199282902678806752087668925017116962070322210432162695486262963136144')
    pi_decimal = Decimal('3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679821480865132823066470938446095505822317253594081284811174502841027019385211055596446229489549303819644288109756659334461284756482337867831652712019091456485669234603486104543266482133936072602491412737245870066063155881748815209209628292540917153643678925903600113305305488204665213841469519415116094330572703657595919530921861173819326117931051185480744623799627495673518857527248912279381830119491298336733624406566430860213949463952247371907021798609437027705392171762931767523846748184676694051320005681271452635608277857713427577896091736371787214684409012249534301465495853710507922796892589235420199561121290219608640344181598136297747713099605187072113499999983729780499510597317328160963185950244594553469083026425223082533446850352619311881710100031378387528865875332083814206171776691473035982534904287554687311595628638823537875937519577818577805321712268066130019278766111959092164201989')
    e_decimal = Decimal('2.7182818284590452353602874713526624977572470936999595749669676277240766303535475945713821785251664274274663919320030599218174135966290435729003342952605956307381323286279434907632338298807531952510190115738341879307021540891499348841675092447614606680822648001684774118537423454424371075390777449920695517027618386062613313845830007520449338265602976067371132007093287091274437470472682084545659292304513823654929637678698712501298448087147617738662991725102877813315458150855743554849327462960554096822190871006007557272990285086043136152853706643888986653256653733379345338978596173630289909194059846036847433364156070272978969490912716927114472700899629686100931872118158498987506178782630108068618073088916821829631962625038779584748632583088686292405370038451261950197530018499869892300508077502418506908300636524354936664499552814928126220534513689903544686925501149683842810521376662802848300208035343822455544558099295434915554133925640758829809492971444935194957848255415540196096881324483119170693836642495706175322294158928047741940757581691905002710309843570807408829799325426875223813262408422648012639315344735049286353316715095815963618845150541178044511489562002898144631612344906173052190112073763433379948045035044408644009837640906058974113380149038686339260238736973321061468052022522353918904521345900596831763428990030438509223991240050805154504419005305729574528219498470591205845468776863235746881182919239154086950028458491889173907452605236761694727274')
    
    # Scale to [0, 1]
    normalized = Decimal(byte_value) / Decimal(255)
    
    # Field harmonics (using float math since Decimal doesn't have sin/cos)
    # We'll use float for trig functions but keep track of exact values
    phi_harmonic = Decimal(str(math.sin(float(normalized * phi_decimal))))
    pi_harmonic = Decimal(str(math.cos(float(normalized * pi_decimal))))
    e_harmonic = Decimal(str(math.sin(float(normalized * e_decimal))))
    
    # Resonance calculation
    resonance = (phi_harmonic + pi_harmonic + e_harmonic) / Decimal(3)
    
    return resonance

def main():
    print("Counting unique resonance values for all 256 bytes...")
    print("=" * 60)
    
    # Method 1: Using float arithmetic
    float_resonances = []
    float_unique = set()
    
    for byte_val in range(256):
        resonance = calculate_resonance(byte_val)
        float_resonances.append(resonance)
        float_unique.add(resonance)
    
    print(f"\nMethod 1 - Float arithmetic:")
    print(f"Total values: 256")
    print(f"Unique values: {len(float_unique)}")
    
    # Method 2: Using Decimal for higher precision
    decimal_resonances = []
    decimal_unique = set()
    
    for byte_val in range(256):
        resonance = calculate_resonance_decimal(byte_val)
        decimal_resonances.append(resonance)
        decimal_unique.add(resonance)
    
    print(f"\nMethod 2 - Decimal arithmetic (50 digits precision):")
    print(f"Total values: 256")
    print(f"Unique values: {len(decimal_unique)}")
    
    # Method 3: Round to different precisions to see where uniqueness emerges
    print(f"\nMethod 3 - Testing uniqueness at different precision levels:")
    for digits in [2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 20]:
        rounded_unique = set()
        for res in float_resonances:
            rounded_unique.add(round(res, digits))
        print(f"  {digits} decimal places: {len(rounded_unique)} unique values")
    
    # Method 4: Check for exact duplicates (within machine epsilon)
    print(f"\nMethod 4 - Checking for exact duplicates:")
    epsilon = 1e-15
    duplicate_count = 0
    
    for i in range(256):
        for j in range(i + 1, 256):
            if abs(float_resonances[i] - float_resonances[j]) < epsilon:
                duplicate_count += 1
                if duplicate_count <= 5:  # Show first 5 duplicates
                    print(f"  Bytes {i} and {j} have nearly identical resonance: {float_resonances[i]:.15f}")
    
    print(f"Total near-duplicates found: {duplicate_count}")
    
    # Method 5: Analyze the distribution
    print(f"\nMethod 5 - Resonance value statistics:")
    min_res = min(float_resonances)
    max_res = max(float_resonances)
    print(f"  Min resonance: {min_res:.15f}")
    print(f"  Max resonance: {max_res:.15f}")
    print(f"  Range: {max_res - min_res:.15f}")
    
    # Sort and show gaps between consecutive unique values
    sorted_unique = sorted(float_unique)
    gaps = []
    for i in range(1, len(sorted_unique)):
        gap = sorted_unique[i] - sorted_unique[i-1]
        gaps.append(gap)
    
    if gaps:
        print(f"  Average gap between unique values: {sum(gaps)/len(gaps):.15f}")
        print(f"  Min gap: {min(gaps):.15f}")
        print(f"  Max gap: {max(gaps):.15f}")
    
    # Final answer
    print("\n" + "=" * 60)
    print(f"FINAL ANSWER: There are {len(float_unique)} unique resonance values")
    print("=" * 60)

if __name__ == "__main__":
    main()