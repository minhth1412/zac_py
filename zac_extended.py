import math
import hashlib
# import pointproofs.py file for the functions
from pointproofs import init_pp, compute_commit_C, random, pairing

# Constant
N = 100     # The upper-bound of values in the database

def init_para(n, P_fp):
    """
    This function is used to initialize the parameters for Bloom Filter.
    The input parameters are:
    - n: the number of elements to be inserted.
    - P_fp: the desired probability of false positive.
    
    This function return these parameters:
    - m: the optimized size for Bloom Filter array.
    - k: the optimized number of hash functions.
    
    Source for reference: https://sagi.io/bloom-filters-for-the-perplexed/#appendix
    """
    # Init
    ln2 = math.log(2)
    ln_fp = math.log(P_fp)
    
    # Calculate the optimized size for Bloom Filter array.
    m = -n * ln_fp / (ln2 ** 2)
    m = int(math.ceil(m))
    
    # Calculate the optimized number of hash functions.
    k = - ln_fp / ln2
    k = int(math.ceil(k))
    
    return m, k

def h(S, k, m):
    """
    This function is used to hash the input string S into hash function h_k.
    The input parameters are:
    - S: the input string to be hashed.
    - k: the index of hash function.
    - m: the size of Bloom Filter array.
    
    This function return the k_th hash value.
    """
    # Init
    N = 0
    for i in range(len(S)):
        N += ord(S[i]) - ord('A')
    N = (N + k) % m
    return N

def set_to_bloom(pp, S):
    """
    This function is used to set the Bloom Filter array with the input string S.
    The input parameters are:
    - pp: the Bloom Filter array.
    - S: the input string to be set.
    - k: the number of hash functions.
    - m: the size of Bloom Filter array.
    """
    hash_values = []
    k = pp['k']
    # Set the Bloom Filter array with k hash values of S
    for i in range(k):
        ind = h(S, i + 1, pp['m'])
        hash_values.append(ind)
        # print(f"Hash value for {S} with k = {i+1}: {ind}")
        pp['bloom_vector'][ind] = 1
        
    return hash_values
    
def bf_gen(S, pp):
    """
    This function is to generate the vector of bits represent Bloom vector after put S into Bloom Filter's hash functions
    The input parameters include S: An input string, and pp: public parameters
    """   
    q = pp['m'] 
    new_bloom_vector = [0] * q
    for i in range(pp['k']):
        ind = h(S, i + 1, q)
        new_bloom_vector[ind] = 1
        
    return new_bloom_vector
    
def read_db():
    """
    This function is used to read the database.
    The database is a dictionary with unique keys and following values:
    """
    # Currently in this function, we use a static database for testing.
    # Later, we can replace this function with a function to read the database from a file.
    # db = {'a': 10, 'b': 10, 'c': 20, 'd': 15, 'e': 10, 'f': 15, 'g': 20}
    
    db = {'a': 3, 'b': 3, 'c': 3}
    return db

# ------------ Commit functions --------------
def com(S, r, pp):
    """
    This function is used to commit the database to Bloom Filter, base on ZAC scheme.
    The input parameters are:
    - S: the input string to be hashed.
    - r: the random number.
    - pp: the public parameters.
    """
    v = set_to_bloom(pp, S)
    return compute_commit_C(v, r, pp['pp_PR'])

def commit(D, db, r, pp):
    """
    This function is used to create commitments for each key groups have the same values to Bloom Filter.
    The input parameters are:
    - D: the dictionary contains the records with the same value, range from 1 to n.
    - db: the database.
    - r: the random number.
    - pp: the public parameters.
    This function return a vector contains the commitments for each key group, and the vector contains these key-group.    
    """
    # Create vector D to store the records with the same value, range from 1 to n
    # In this setup, D[0] contains all keys in the database, instead of D[n + 1]
    cm = []
    for i in db:
        if db[i] in D:
            D[db[i]] = D[db[i]] + [i]
        else:
            D[db[i]] = [i]
        D[0] = D[0] + [i]
    for i in D:
        print(f"Records with value {i}: {D[i]}")
    
    # Commitment for all keys: C_0 = ZAC.Com(D_0, r, pp)
    cm.append(com(D[0] + [str(len(D[0]))], r, pp))
    
    
    # Create commitment for each key group
    for i in range(1, N + 1):
        if (i in D):
            # cm[i] = ZAC.Com(D_i + |D_i|, r, pp)
            # For example: D_i = [a, b, e], |D_i| = 3	=> D_i + |D_i| = [a, b, e, 3]
            # 3 here is in string type
            cm.append(com(D[i] + [str(len(D[i]))], r, pp))
        else:
            # cm[i] = ZAC.Com({0, r_i}, r, pp)
            # here, r_i is a random number. In this project, it will be 1 (for testing purpose)
            cm.append(com([str(0), str(1)], r, pp))
            
    return cm
# --------------------------------------------

def query_db(QC, db):
    """
    This function is used to query the database with the query Q.
    The input parameters are:
    - QC: the query Q, in this work, it is the key x.
    - db: the database.
    
    This function return the record with key x if exists, otherwise return [].
    """
    if QC in db:
        return [QC, db[QC]]
    else:
        return []

# ------------ Proof functions ---------------
def proveM(cm, S, S_hat, r, pp):
    I = set()           # Set updating is automatic remove the duplicated element
    for s in S_hat:
        I.update(h(s,i + 1,pp['m']) for i in range(pp['k']))
        
    v = bf_gen(S, pp)
    
    proofs = {}
    
    # print(I)
    for i in I:
        proofs[i] = pr_prove(i,v,r,pp)
        # print proof
        # print(f"proof {i}: {proofs[i]}")
        
    sub_v = [v[i] for i in I]           # This is v[I]
    sub_proof = [proofs[i] for i in I]
    # Aggregate the proofs into 1 proof
    proof = pr_aggregate(cm, I, sub_v, sub_proof, pp)
    return I,v,[proof, [0]]
    
def pr_prove(i, v, r, pp):
    """
    Compute pi_i = g_1^{Σ: l∈[q-1]-{i} (v_l * alpha^{q + 1 - i + l} + r * alpha^{q + 1 - i + q})}
    """
    alpha = pp['pp_PR']['alpha']
    p = pp['pp_PR']['p']
    q = pp['m']
    g1 = pp['pp_PR']['g1']
    hat_value = 0
    for ell in range(q):
        if ell != i:  # Exclude i from the range [q-1]
            term = (v[ell] * pow(alpha, q + 1 - i + ell, p)) % p
            hat_value += term
    
    # Add the term r * alpha^(q+1-i+q)
    hat_value += (r * pow(alpha, q + 1 - i + q, p)) % p
    
    # Return the proof
    return pow(g1, hat_value, p) % p

def pr_aggregate(cm, S, v, proofs, pp):
    """
    This function is used to aggregate the proofs into 1 proof.
    The input parameters are:
    - cm: the commitment.
    - I: the set of indices.
    - v: the vector of bits.
    - proofs: the proofs.
    This function return the aggregated proof.
    """
    t = []
    p = pp['pp_PR']['p']
    # The String to be hashed will be: i + cm + 'S1,S2,...,Sl' + 'v1,v2,...,vl', with l = I.len()
    # For example:
    for i in S:
        flatten_str = str(i) + str(cm) + ','.join(map(str, S)) + ','.join(map(str, v))
        t.append(int(hashlib.sha256(flatten_str.encode()).hexdigest(), 16) % p)
        # t.append(h(flatten_str, 1, pp['m']))  
    
    aggr_proof = 1
    p = pp['pp_PR']['p']
    for i in range(len(S)):
        aggr_proof *= pow(proofs[i], t[i], p)
        aggr_proof = aggr_proof % p
        # print(f"aggr_proof: {aggr_proof}")

    return aggr_proof    

def proveN(cm, S, S1, r, pp):
    # Extract the variables from the proveM function
    I,v,proof_hat = proveM(cm, S, S1, r, pp)
    proof = proof_hat[0]
    # res <-- I, where v[x] = 0
    res = [i for i in I if v[i] == 0]
    print(f"v: {v}")
    print(f"res: {res}")
    return [proof, res]

# In this project, we only work with the QC1, which is the represent of the query Q1:
#    Q1: Return the record with key x.
#    Which can be [db[x]] if exists.
#    Otherwise, return [].
def proveQ(cm, D, QC, db, r, pp):
    Ret = query_db(QC, db)
    # Passed the condition QC = QC1, and QC = x
    if Ret == []:
        # C_{n+1} <- cm[0]
        cm_for_all = cm[0];
        # proof = ZAC.ProveN(cm_for_all, D[0], [x], r, pp), this will prove that x is not in the database, or: QC not in D[0]
        return proveN(cm_for_all, D[0], [QC], r, pp)
    else:
        x, v = Ret
        c_v = cm[v]     # Commitment of D_v
        
        # proof = ZAC.ProveM(c_v, D[v], [x], r, pp), this will prove that x is in D_v, or implies that x is in set of keys K.
        _,_,proof = proveM(c_v, D[v], [x], r, pp)
        return proof   

# --------------------------------------------

# ------------ Verify functions --------------

def pr_verify(C, S, m, proof_hat, pp):
    t = []
    p = pp['pp_PR']['p']
    
    for i in S:
        flatten_str = str(i) + str(C) + ','.join(map(str, S)) + ','.join(map(str, m))
        t.append(int(hashlib.sha256(flatten_str.encode()).hexdigest(), 16) % p)
        # t.append(h(flatten_str, 1, pp['m']))
        
    alpha = pp['pp_PR']['alpha']
    g2 = pp['pp_PR']['g2']
    
    q = pp['m']
    gT = pp['pp_PR']['gt']
    
    # Compute the left side: e(C, g_2^{Σi∈S(α^{q+1−i}t_i)})
    left_exponent = sum(pow(alpha, q + 1 - i, p) * t_i % p for i, t_i in zip(S, t)) % p
    left = pairing(C, pow(g2, left_exponent, p), p)
    
    # Compute the right side: e(π_hat, g_2) · g_T^{α^{q+1}Σi∈Sm_i*t_i}
    right_exponent = (pow(alpha, q + 1, p) * sum(m_i * t_i % p for m_i, t_i in zip(m, t)) % p) % p
    right = (pairing(proof_hat, g2, p) * pow(gT, right_exponent, p)) % p
    
    # Compare the left and right sides
    print(left)
    print(right)
    return left == right

def verifyM(cm, S_hat, proof_hat, pp):
    I = set()           # Set updating is automatic remove the duplicated element
    for s in S_hat:
        I.update(h(s,i + 1,pp['m']) for i in range(pp['k']))
       
    # Create empty bloom filter array, and then set v_i = 1 with i in I
    v = [0]*pp['m']
    sub_v = []
    for i in I:
        v[i] = 1
        # Below is the creation of a sub_vector contains |I| values to represent v[I], for the call pr_verify
        sub_v.append(1)

    print(f"sub_v for verifyM is {sub_v}")
    proof = proof_hat[0]
    bool_result = pr_verify(cm, I, sub_v, proof, pp)
    return bool_result

def verifyN(cm, S_hat, proof_hat, pp):
    proof, set_x = proof_hat
    I = set()           # Set updating is automatic remove the duplicated element
    for s in S_hat:
        I.update(h(s,i + 1,pp['m']) for i in range(pp['k']))
        
    # Create empty bloom filter array, and then set v_i = 1 with i in I, and i not in set_x
    v = [0]*pp['m']
    sub_v = []
    for i in I:
        if i not in set_x:
            v[i] = 1
        # Below is the creation of a sub_vector contains |I| values to represent v[I], for the call pr_verify
        sub_v.append(1)
        
    return set_x != [] and pr_verify(cm, I, sub_v, proof, pp)

def verifyQ(cm, QC, Ret, proof_hat, pp):
    # This function passes the condition QC = QC1
    # In this work, QC = x and will be modified in the future work.
    if Ret == []:
        # C_{n+1} <- cm[0]
        cm_for_all = cm[0];
        # return ZAC.VerifyN(cm_for_all, [x], proof_hat, pp)
        # In future work, QC contains x, so that it will be put in the below function instead of using Ret
        return verifyN(cm_for_all, [QC], proof_hat, pp)
    else:
        cm_v = cm[Ret[1]]     # Commitment of D_v
        # Below function use Ret[0] because Ret != [], and Ret[0] is the record with key x
        return verifyM(cm_v, [Ret[0]], proof_hat, pp)

# --------------------------------------------

# ------------- Main function -------------
if __name__ == "__main__":
    
    # ------------- Initialize the start parameter and function call -------------
    # The number of records in database
    n = 7
    # The desired probability of false positive
    fp = 0.01
    
    # Call the function to initialize the parameters for Bloom Filter
    m, k = init_para(n, fp)
    
    # Create database
    db = read_db()
    
    # Create Bloom Filter array with m bits 0
    bloom = [0] * m
    
    # Create dictionary D to store the records with the same value, range from 1 to n
    D = {0:[]}
    
    ### ---- pp <- ZAC.Init(1^lambda, n) ----
    # Create public parameters for ZAC scheme: pp, include:
    # m, k: the parameters for Bloom Filter
    # pp_PR: public parameters from pointproofs.py
    # This pp is not contain hash function(Different from paper), because the hash function is defined separately in a function
    #   in this file. And the scheme using hash function is quite different too.
    pp = {
        'm': m,
        'k': k,
        'bloom_vector': bloom,
        'pp_PR': init_pp(128, m)
        # 128 is the security parameter that is chosen based on the desired security level
    }
    
    # A random number r
    r = random.randint(1, pp['pp_PR']['p'] - 1)
    # ----------------------------------------------------------------------------
    
    ## ---- cm <- ZKEDB.CommitDB(D, db, pp) ----
    cm = commit(D, db, r, pp)
    # for i in range(N + 1):
    #     if i in D:
    #         print(f"D[i]: {D[i]}")
    #     else:
    #         print(f"D[i]: {[]}")
    #     print(f"Commitment for key group {i}: {cm[i]}")
    
    
    
    
    # ------------- Place to test -------------
    # Test set_to_bloom function
    # for key in db.keys():
    #     set_to_bloom(pp, key, k, m)
    
    # Test the optimized parameters for Bloom Filter    
    print(f"Optimized size for Bloom Filter array: {m}")
    print(f"Optimized number of hash functions: {k}")
    
    
    # Test for proveQ function
    # The query Q1: Return the record with key x = 'a'.
    # Which can be [db[x]] if exists.
    # Otherwise, return [].
    
    # Future work will change this QC into a function for checking query, and return the desired value.
    QC = 'a'
    Ret = query_db(QC, db)
    # Print Ret
    print(f"\nQuery result for key {QC}: {Ret}")
    
    # Create proof_hat for QC
    proof_hat = proveQ(cm, D, QC, db, r, pp)
    print(f"Proof_hat for query Q1: {proof_hat}")
    
    # Check the proof with verifyQ function
    res = verifyQ(cm, QC, Ret, proof_hat, pp)
    
    if res == True:
        # Announce that x is in db, and print the value of x
        print(f"Query Q1: {QC} is in the database.")
        print(f"Value of {QC}: {Ret[1]}")
    else:
        # Announce that x is not in db
        print(f"Query Q1: {QC} is not in the database.")
    
    print("End of file.")
    # -----------------------------------------