import random
import math
import time
import hashlib
import pandas as pd

def prob_fp(k, q, N):
    """
    This function calculate and return: (1 - (1 - 1/q)^kN)^k
    
    , which is the probability of False-positive
    """
    return (1 - ((1 - 1/q)**(k*N)))**k
    

def find_q_k_with_theory(N):
    """
    This function calculates the optimized (q, k) for Bloom Filter.
    Input includes:
    - n: The number of records in database
    
    """
    # ------------------- Below is the way to calculate the optimal q,k with given n
    # First, initialize those parameters
    min_prob_fp = prob_fp(20,10*N,N)
    optimal_q = 10*N
    optimal_k = 20
    
    # Then, create loop to determine the optimal q, k.
    # Known that:
    #   q is the amount of bits represent Bloom Filter, 1 <= q <= N
    #   k is the amount of hash functions in Bloom Filter, 1 <= k <= q
    for q in range(1, 10*N + 1):
        for k in range(1, 20):
            temp = prob_fp(k, q, N)
            # print(f"With q = {q}, k = {k}, Pr = {temp}")
            if min_prob_fp > temp:
                min_prob_fp = temp
                optimal_q = q
                optimal_k = k
    
    
    
    # ------------ Below is the way to calculate the optimal q,k with given n and fp
    # Based on 
    # ln2 = math.log(2)
    # lnp = math.log(fp)
    # optimal_k = -lnp/ln2
    # optimal_q = -n*lnp/((ln2)**2)
    
    # Round them with ceiling
    optimal_q = int(math.ceil(optimal_q))
    optimal_k = int(math.ceil(optimal_k))
    
    # Return q, k
    return min_prob_fp, optimal_q, optimal_k

                

def generate_name():
    """This function denerate a random name with characters in alphabet, and the key size is random from 1 to 3 

    Returns:
        key: string type, a random key
    """
    key_length = random.randint(1, 3)
    key = ''.join(random.choices('abcdefghijklmnopqrstuvwxyz', k=key_length))
    return key

def h(s, i, q):
    """
    This function is used to hash the input string S into hash function h_k.
    The input parameters are:
    - s: the input string to be hashed.
    - i: the index of hash function.
    - q: the size of Bloom Filter array.
    
    This function return the i_th hash value.
    """
    # Init for testing with harcode dataset, basic hash function, 
    # this have weakness that the return hashed integers of a string S for k hash functions will have adjacent indexes
    
    # N = 0
    # for ind in range(len(s)):
    #     N += ord(s[ind]) - ord('A')
    # N = (N + i) % q
    # return N
    

    # Init for imported dataset, more complex hash function
    if i % 3 == 0:
        modified_string = s + str(i)
    elif i % 3 == 1:
        modified_string = str(i) + s
    else:
        modified_string = s[:len(s)//2] + str(i) + s[len(s)//2:]
                
    # Encode the modified string to bytes
    byte_string = modified_string.encode()
                
    # Create a SHA-256 hash object
    sha256_hash = hashlib.sha256()
                
    # Update the hash object with the byte string
    sha256_hash.update(byte_string)
                
    # Get the hexadecimal digest of the hash
    hex_digest = sha256_hash.hexdigest()
                
    res = int(hex_digest, 16) % q
                
    return res
        

def set_to_bloom(k, q, d):
    """
    This function is used to set the Bloom Filter array with the input string S.
    The input parameters are:
    - k: the number of hash functions.
    - q: the size of Bloom Filter array.
    - d: the set represent for dv that need to be inserted into Bloom Filter set
    """
    
    bloom = [0]*q
    # S = "".join(d)      
    # Set the Bloom Filter array with k hash values of S
    for S in d:
        for i in range(k):
            ind = h(S, i + 1, q)
            # print(f"Hash value for {S} with k = {i+1}: {ind}")
            bloom[ind] = 1
    
    return bloom

def check(bloom, key, k, q):
    """This function is to check that key is in the BF set or not"""
    for i in range(k):
        ind = h(key, i + 1, q)
        # print(f"Hash value for {S} with k = {i+1}: {ind}")
        if bloom[ind] == 0:
            return False
        
    return True

def find_q_k_with_db(q, k, Dv, vec_key):
    """
    This function calculates the optimized (q, k) for Bloom Filter, based on result from theory and the database for checking.
    Input includes:
    - q: The amount of bits represent for Bloom Filter array.
    - k: The amount of hash functions in Bloom Filter (h_1, h_2,...,h_k)
    - Dv: The dictionary that each value set has share the same key as value in database, 
         where each element in that set value is unique key
    - vec_key: a vector contains keys of current database
    
    The function returns the fixed optimal q and k that fit the current database.
    """
    
    # Initialize the parameters
    delta = 5
    min_total_fp = 1
    ret_q = q
    ret_k = k
    
    # To avoid q_star, k_star have negative value, use these variables to make adjustment in below loop
    min_range_k = abs(min(0, ret_k - delta))
    min_range_q = abs(min(0, ret_q - delta))
    
    # Because the range start from 1 for both q, k
    if min_range_k != 0:
        min_range_k = min_range_k + 1
    if min_range_q != 0:
        min_range_q = min_range_q + 1
    
    for k_star in range(k - delta + min_range_k, k + delta + 1 + min_range_k):
        for q_star in range(q - delta + min_range_q, q + delta + 1 + min_range_q):
            total_false_positive = 0
            
            for i in Dv:
                count = 0
                
                bloom = set_to_bloom(k_star, q_star, Dv[i])
                for _ in range(1000):
                    # This create random key for hardcode dataset
                    # random_key = generate_name()
                    
                    # This create random key for import dataset, which is choosen from vector of keys in current database: 
                    random_key = random_key = random.choice(list(vec_key))
                    
                    # Compare the matching of random_key existence in both bloom of Dv and current Dv
                    # Check in D[i] means that this represent a query for a key K to have a particular value v
                    # For example, a dataset include unique names and their correspond age. The query will be: Does 'A' have age v?
                    if check(bloom, random_key, k_star, q_star) != (random_key in Dv[i]):
                        count += 1
                        
                # Update the total_false-positive
                false_positive = count/1000
                total_false_positive += false_positive
            
            # Update optimal q and k
            if min_total_fp > total_false_positive:
                min_total_fp = total_false_positive
                ret_q = q_star
                ret_k = k_star
            
    print(f"minimum total fp: {min_total_fp}")
    return min_total_fp, ret_q, ret_k
                    
def create_Dv(db):
    D = {0:[]}
    for i in db:
        if db[i] in D:
            D[db[i]] = D[db[i]] + [i]
        else:
            D[db[i]] = [i]
        D[0] = D[0] + [i]
    # for i in D:
    #     print(f"Records with value {i}: {D[i]}")
    return D

def read_db():
    """
    This function is used to read the database.
    The database is a dictionary with unique keys and following values:
    """
    # Currently in this function, we use a static database for testing.
    # Later, we can replace this function with a function to read the database from a file.
    # db = {'a': 10, 'b': 10, 'c': 20, 'd': 15, 'e': 10, 'f': 15, 'g': 20}
    
    # --------------------- Data imported-----------------
    # Define the range of rows to import (100 to 300, inclusive)
    # The range can be modified for other tests
    # Random start_row from 1 to 100000
    start_row = random.randint(1, 100000)
    # Random end_row = start_row + random(1,3000)
    end_row = start_row + random.randint(30,3000)


    # Calculate the number of rows to import
    num_rows = end_row - start_row + 1

    # Read the specified range of rows from the CSV file, and put it in dataframe
    df = pd.read_csv('Crimes_-_2001_to_Present.csv', skiprows=range(1, start_row), nrows=num_rows)

    # Specify the columns you want to use as the dictionary's keys and values
    key_column = 'ID'
    value_column = 'Ward'

    # Convert the specified columns into a dictionary
    db = df.set_index(key_column)[value_column].to_dict()
    
    # Convert the set key from int into string
    db = {str(k): v for k, v in db.items()}
    
    # Create keys set for testing purpose
    key_set = set(df[key_column].astype(str))
    
    return key_set, db, num_rows

if __name__ == "__main__":
    data = {
        'min_fp': [],
        'q founded': [],
        'k founded': [],
        'time checking with database': []
    }
    
    vec_key, db, item_counts = read_db()
    print(item_counts)
    # N = 50      # Since the range of ward in real dataset has maximum equals 50
    # desired_fp = 0.01
    # min_prob_fp, optimal_q, optimal_k = find_q_k_with_theory(item_counts, desired_fp)
    min_prob_fp, optimal_q, optimal_k = find_q_k_with_theory(item_counts)
    
    print("q and k found with theory:")
    print(f"Optimal q = {optimal_q}")
    print(f"Optimal k = {optimal_k}")
    print(f"The minimum probability of False-positive found: {min_prob_fp}")
    
    # Create Dv set
    Dv = create_Dv(db)
    
    # find_q_k_with_db(optimal_q, optimal_k, db)
    for _ in range(100):
        # Start the timer
        start_time = time.time()
        
        min_fp,q,k = find_q_k_with_db(optimal_q,optimal_k,Dv,vec_key)
        
        # Stop the timer
        end_time = time.time()
        
        print("q and k found with running database test:")
        print(f"Optimal q found = {q}")
        print(f"Optimal k found = {k}")
        # Calculate the elapsed time
        elapsed_time = end_time - start_time

        print(f"Elapsed time running database test: {elapsed_time} seconds")
        
        data['min_fp'].append(min_fp)
        data['q founded'].append(q)
        data['k founded'].append(k)
        data['time checking with database'].append(elapsed_time)
    
    df = pd.DataFrame(data)
    
    # excel_file = 'test_result_hardcode_with_n_equals_' + str(item_counts) + '.xlsx'
    excel_file = 'test_result_with_n_equals_' + str(item_counts) + '_using_data_imported.xlsx'
    
    df.to_excel(excel_file, index=False)
    
    print(f"Data testing exported to {excel_file}")