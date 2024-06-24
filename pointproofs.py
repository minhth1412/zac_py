from Crypto.Util.number import getPrime
from Crypto.Random import random

def pairing(g1, g2, p):
    # Compute the bilinear pairing e(g1, g2)
    gt = pow(g1, g2, p)
    return gt

def init_pp(lambda_param, q):
    # Initialize a prime order p for the multiplicative group
    p = getPrime(lambda_param)

    # Generate a random element alpha in Zp
    alpha = random.randint(1, p-1)

    # Define generators g1 and g2 for groups G1 and G2 respectively
    g1 = random.randint(1, p-1)
    g2 = random.randint(1, p-1)

    # Compute g1^alpha, g2^alpha, ..., g1^(alpha^q), g2^(alpha^q)
    g1_alpha = [(g1 * pow(alpha, i, p)) % p for i in range(1, q + 1)]
    g2_alpha = [(g2 * pow(alpha, i, p)) % p for i in range(1, q + 1)]

    # Compute additional elements: g1^(-alpha^q), g1^(alpha^(q+1)), ..., g1^(alpha^(2q))
    g1_alpha_neg = pow(g1, -(pow(alpha, q, p)), p)
    g1_alpha_extended = [(g1 * pow(alpha, q + i, p)) % p for i in range(1, q + 1)]

    # Create the public parameters as a dictionary for later uses
    pp_PR = {
        'g1': g1,
        'g2': g2,
        'g1_alpha': g1_alpha,
        'g2_alpha': g2_alpha,
        'g1_alpha_neg': g1_alpha_neg,
        'g1_alpha_extended': g1_alpha_extended,
        'alpha': alpha,
        'p': p,
        'gt': pairing(g1, g2, p)
    }

    return pp_PR

def compute_commit_C(m, r, pp_PR):
    # Extract public parameters
    g = pp_PR['g1']
    alpha = pp_PR['alpha']
    p = pp_PR['p']
    q = len(m)

    # Step 1: Compute the term r * alpha^q
    r_alpha_q = r * pow(alpha, q, p) % p

    # Step 2: Compute the sum of m_i * alpha^i for i in [1, q-1]
    sum_m_alpha = sum((m[i] * pow(alpha, i, p)) % p for i in range(q)) % p

    # Step 3: Compute the final exponent (r * alpha^q) + sum(m_i * alpha^i)
    final_exponent = (r_alpha_q + sum_m_alpha) % p

    # Step 4: Compute C = g^(final_exponent) % p
    C = pow(g, final_exponent, p)

    return C

# Example usage
lambda_param = 128  # security parameter
q = 5  # degree of the polynomial

# Initialize public parameters
pp = init_pp(lambda_param, q)
#print("Public Parameters (pp):", pp)

# # Example parameters for compute_commit_C
# r = random.randint(1, pp['p']-1)  # random value r
# m = [random.randint(1, pp['p']-1) for _ in range(q)]  # message coefficients m_i

# # Compute commit C
# C = compute_commit_C(m, r, pp)
# print(f"Computed C: {C}")