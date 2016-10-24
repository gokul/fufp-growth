# encoding: utf-8

"""
A Python implementation of the FUFP-growth algorithm.
B. Gokulakrishnan
"""

from collections import defaultdict, namedtuple
from itertools import chain, combinations, imap
import math
import time

from FUFPTree import FUFPTree
from FPNode import FPNode

ctr = 0

G_tree = FUFPTree()
G_old_db = dict()
G_d = 0
G_min_sup_per = 0.1
G_old_large_HT = dict()


def find_initial_frequent_itemsets(transactions, minimumSupport):

    items = defaultdict(lambda: 0) # mapping from items to their supports
    processed_transactions = []
    
    le = 1
    global ctr
    global minimum_support
    mapped_db = dict() #The Old-DB to be passed to FUFP-tree
    
    for transaction in transactions:
        processed = []
        for item in transaction:
            items[item] += 1
            processed.append(item)
            
            if mapped_db.has_key(item):
                list = mapped_db.get(item)
                list.append(transaction)
            else:
                list = []
                list.append(transaction)
                mapped_db[item] = list    
            
        processed_transactions.append(processed)
        
        if len(transaction)>le:
            le = len(transaction)
            ctr += 1
            
    #=====
    old_all = dict(items)
    d = len(processed_transactions)
    #=====
    
    minimum_support = int(math.ceil(d*float(minimumSupport/100)))
    # Remove infrequent items from the item support dictionary.
    items = dict((item, support) for item, support in items.iteritems()
        if support >= minimum_support)

    # Build our FP-tree. Before any transactions can be added to the tree, they
    # must be stripped of infrequent items and their surviving items must be
    # sorted in decreasing order of frequency.
    def clean_transaction(transaction):
        transaction = filter(lambda v: v in items, transaction)
        transaction.sort(key=lambda v: items[v], reverse=True)
        return transaction
  
    master = FUFPTree()
    for transaction in imap(clean_transaction, processed_transactions):
        master.add(transaction)
         
    #Header tables for the OLD DB, in the form {item: count}
    old_large = items
    #old_small = diff(old_all, items)
    
    #master = completed FP-tree for the OLD DB
    # Search for frequent itemsets, and yield the results we find.
    
    final = dict()

    for itemset, support in find_with_suffix(master, []):
        final[frozenset(itemset)] = support
       
    return final, master, mapped_db, d, old_large

def find_with_suffix(tree, suffix):
     for item, nodes in tree.items():
        support = sum(n.count for n in nodes)
        if support >= minimum_support and item not in suffix:
            # New winner!                
            found_set = [item] + suffix
            yield (found_set, support)
            # Build a conditional tree and recursively search for frequent
            # itemsets within it.
            cond_tree = conditional_tree_from_paths(tree.prefix_paths(item),
                minimum_support)
            for s in find_with_suffix(cond_tree, found_set):
                yield s # pass along the good news to our caller


def conditional_tree_from_paths(paths, minimum_support):
    """Builds a conditional FP-tree from the given prefix paths."""
    tree = FUFPTree()
    condition_item = None
    items = set()

    # Import the nodes in the paths into the new tree. Only the counts of the
    # leaf notes matter; the remaining counts will be reconstructed from the
    # leaf counts.
    for path in paths:
        if condition_item is None:
            condition_item = path[-1].item

        point = tree.root
        for node in path:
            next_point = point.search(node.item)
            if not next_point:
                # Add a new node to the tree.
                items.add(node.item)
                count = node.count if node.item == condition_item else 0
                next_point = FPNode(tree, node.item, count)
                point.add(next_point)
                tree._update_route(next_point)
            point = next_point

    assert condition_item is not None

    # Calculate the counts of the non-leaf nodes.
    for path in tree.prefix_paths(condition_item):
        count = None
        for node in reversed(path):
            if count is not None:
                node._count += count
            count = node.count

    # Eliminate the nodes for any items that are no longer frequent.
    for item in items:
        support = sum(n.count for n in tree.nodes(item))
        if support < minimum_support:
            # Doesn't make the cut anymore
            for node in tree.nodes(item):
                if node.parent is not None:
                    node.parent.remove(node)

    # Finally, remove the nodes corresponding to the item for which this
    # conditional tree was generated.
    for node in tree.nodes(condition_item):
        if node.parent is not None: # the node might already be an orphan
            node.parent.remove(node)

    return tree


"""TREE CONSTRUCTION FOR FUFP-GROWTH
ARGS: 
    tree = previous FUFP-tree structure
    old_db = mapped U DB from the previous run 
    d = total number of all previous transactions
    new_tr = new list of sessions
    old_large_HT = previous header table of large items

"""
def fufp_growth(tree, old_db,d, new_tr, old_large_HT):
    
    global ctr
    le = 1
    
    insert_items = []
    rescan_items = []
         
    U_large_HT = old_large_HT.copy() #The Header table
    
    U_db = old_db.copy()            #Combined DB
    new_db = dict()                 #Incoming DB
    
    items = defaultdict(lambda: 0) # mapping from items to supports for ALL trans.
    t = len(new_tr)
       
    new_minimum_support = int(math.ceil(t*float(G_min_sup_per/100)))
    overall_minimum_support = int(math.ceil((d+t)*float(G_min_sup_per/100)))
    
    """ CASE 1 in paper """
    def large_large(item): 
        Su = old_large_HT[item] + items.get(item)
        #print item, "is in large-large"
        U_large_HT[item] = Su
        insert_items.append(item)
                
    """ CASE 2 in paper """    
    def small_large(item):
        Su = old_large_HT[item] + items.get(item)
        #print item, "is in small_large"
        if Su >= overall_minimum_support:
            U_large_HT[item] = Su
            insert_items.append(item)
        else:
            del U_large_HT[item]             
            """ TREE MANIPULATION. POTENTIALLY DANGEROUS """
            #print "Removing", item
            for node in tree.nodes(item):
                if node.parent is not None:
                    node.parent.remove(node)
        
    """ CASE 3 in paper """    
    def large_small(item):
        if old_db.has_key(item):
            Sd = len(old_db[item])
        else:
            Sd = 0
        Su = Sd + items.get(item)
        #print item, "is in large_small"
        if Su >= overall_minimum_support:
            U_large_HT[item] = Su          #deviant step
            insert_items.append(item)
            rescan_items.append(item)
            
            
    def clean_transaction(transaction):
        transaction = filter(lambda v: v in U_large_HT, transaction)
        transaction.sort(key=lambda v: U_large_HT[v], reverse=True)
        return transaction
    
    for transaction in new_tr:
        for item in transaction:
            items[item] += 1
            if new_db.has_key(item):
                list = new_db.get(item)
                list.append(transaction)
            else:
                list = []
                list.append(transaction)
                new_db[item] = list
                
        if len(transaction)>le:
            le = len(transaction)
            ctr += 1       
    
    ll = 0
    ls = 0
    sl = 0
    ss = 0        
    for item in items.keys():
        if items.get(item) >= new_minimum_support:
            if old_large_HT.has_key(item):
                ll += 1
                """"large in new and large in old"""
                large_large(item)
            else:
                ls += 1
                """"large in new but small in old"""
                large_small(item)
        else:
            if old_large_HT.has_key(item):
                sl += 1
                """small in new but large in old"""
                small_large(item)
            else:
                """small in new and old - not considered"""
                ss += 1
                #print item, "didn't make the cut."

    """ Adding new items to the tree """
    new_transactions = []
    old_transactions = []
    
    print 'Large in both old and new DBs:',ll
    print 'Large in new but small in old:',ls
    print 'Small in new but large in old:',sl
    print 'Small in both; not considered:',ss
    
    for item in rescan_items:
        transactions = old_db[item]
        for transaction in transactions:
            if not transaction in old_transactions:
                old_transactions.append(transaction)
    
    for item in insert_items:
        transactions = new_db[item]
        for transaction in transactions:
            if not transaction in new_transactions:
                new_transactions.append(transaction)
                
    for transaction in imap(clean_transaction, old_transactions):
            #print 'old', transaction
            tree.pseudo_add(transaction)                
     
    for transaction in imap(clean_transaction, new_transactions):
            #print 'new', transaction
            tree.add(transaction)
             
    """ Code for computing old_db U new_db, based on transactions for each item """
    for item in items.keys():
        transactions = new_db.get(item)
        for transaction in transactions:
            trans = frozenset(transaction)
            if U_db.has_key(item):
                list = U_db.get(item)
                frozenlist = []
                for itemset in list:
                    frozenlist.append(frozenset(itemset))
                if trans not in frozenlist:
                    list.append(transaction)
            else:
                U_db[item] = transactions  
    
    #tree.inspect()
    new_freq_patterns = dict()
    
    for itemset, support in find_with_suffix(tree, []):
        new_freq_patterns[frozenset(itemset)] = support
#   FOR ARG ORDER fufp_growth(tree, old_db,d, new_tr, min_sup_per, old_large_HT):
    
    G_tree = tree
    G_old_db = U_db
    G_d = d+t
    G_old_large_HT = U_large_HT
    
    return new_freq_patterns

#===================================================================================== 
#===============================RECOMMENDATION CODE===================================

def generateRules(data, conf):
    rulez = []
    holder = dict()
    counter = 0;
    def getSupport(pat):
        if not data.has_key(pat):
            return -1
        support = data[pat]
        return support
    
    def subset(arr):
        """ Returns non empty subsets of arr"""
        return chain(*[combinations(arr,i + 1) for i,a in enumerate(arr)])
    
    
    while counter <= ctr:
        counter +=1
        holder[counter] = dict()
    
    for item in data:
        _subsets = map(frozenset, [x for x in subset(item)])
        for element in _subsets:
            remain = item.difference(element)
            if len(remain) > 0:
                itemSup = float(getSupport(item))
                elemSup = float(getSupport(element))
                if (itemSup < 0 or elemSup < 0):
                    continue
                confidence = itemSup /elemSup
                if confidence >= conf:
                    rulez.append(((tuple(element), tuple(remain)),
                                               confidence))
                    length = len(element)
                    rules = holder[length]
                    if rules.has_key(element):
                        options = rules.get(element)
                        options[remain]=confidence
                    else:
                        options=dict()
                        options[remain]=confidence
                        rules[element]=options 
    return rulez, holder

def evaluate(recommendationSet,actual,average,count,correct):
    count+=1
    if actual in recommendationSet:
        average = calculateAccuracy(1,average,count)
        correct+=1
        return (average,count,correct)
    else:
        average=calculateAccuracy(0,average,count)
        return (average,count,correct)
    
def calculateAccuracy(correct,average,count):
        return ((int(count)-1)*float(average)+int(correct))*100/int(count)

              
def recommend(session, holder):
    sessionSet = frozenset(session)
    length = len(sessionSet)
    if length > len(holder):
        return ""
    ruleSet = holder[length]
    if ruleSet.has_key(sessionSet):
        resultSet = ruleSet[sessionSet]
        recommendlist=frozenset()
        for key,item in resultSet.items():
            recommendlist|=key
        return recommendlist
    return ""

def fufpgrowthRecommender(sessions, holder):
    #file_iter = open(sessions, 'rU')
    count=0
    average=0
    total = 0
    correct =0
    
    for elem in sessions:
        iterator =0
        sessionList =[]
        if len(elem)>1:
            for item in elem:
                iterator +=1
                #print "Recommender Iterator : ", iterator
                if iterator==(len(elem)-1):
                    break
                sessionList.append(item)
                #print "Recommender session : ", sessionList
                recommendationList = recommend(sessionList, holder)
                total+=1
                #print "Recommender recommendation : ", recommendationList
                if not (len(recommendationList)<1):
                    result= evaluate(recommendationList, elem[iterator], average, count,correct)
                    average=result[0] 
                    count=result[1] 
                    correct=result[2]
                    
    if not (count == 0 or total == 0):                
        accuracy = float(correct)/float(count)
        coverage = float(count)/float(total)
#        print "Average : ", average
        print "     ---     "
        print "---> Total : ",total
        print "---> Count : ", count
        print "---> Correct : ", correct
        print "------> Accuracy :  %.3f" % (accuracy*100)
        print "------> Coverage :  %.3f"  % (coverage*100)
        timer()

#=====================================================================================      

def fufp_growth_init(trainingset, support, confidence, cutoff, csv_testingset):
    
    testingset = list(csv_testingset)
    counter = 1
    top = 0
    mid = cutoff
    bottom = len(testingset)
    chunks = []
    print '\nSplitting the training set'
    while(mid < bottom):
        chunks.append(testingset[top:mid])
        top = mid
        mid += cutoff
    if(mid >= bottom):
        chunks.append(testingset[(mid-cutoff):bottom]) 
           
    total = len(chunks)
    print 'Result:',total,'portions' 
    print '\nBuilding initial FUFP-tree'   
    freq_pats, fufptree, old_db, length, old_ht = find_initial_frequent_itemsets(trainingset, support)
    #testlist = [['a','b','d','e','g'], ['c','e','i','f'], ['a','b','d','h'], ['a','b','c','d','g'], ['b','c','d','i']]
    
    G_tree = fufptree
    G_old_db = old_db
    G_d = length
    G_min_sup_per = support
    G_old_large_HT = old_ht
        
    print '\nBegin continuous FUFP-growth'
    
    for chunk in chunks:
        print '\nRun',counter, 'of',total
        counter += 1
        new_freq_pats = fufp_growth(G_tree, G_old_db, G_d, chunk, G_old_large_HT)
        
        ruleset, holder = generateRules(new_freq_pats, confidence)
        fufpgrowthRecommender(chunk, holder)
    
    
def timer():
    timeList = []
    timeList.append(time.time())
    if len(timeList)%2 == 0:
        print 'Time elapsed: ' + str(round(timeList[-1] - timeList[-2],4)) + ' s.'    

if __name__ == '__main__':
    from optparse import OptionParser
    import csv

    p = OptionParser(usage='%prog data_file')
    
    p.add_option('-s', '--support', dest='minsup', type='float',
        help='Minimum itemset support (default: 0.1)')
    p.set_defaults(minsup=0.1)
    
    p.add_option('-c', '--confidence', dest='minconf', type='float',
         help='Minimum confidence threshold for association rules (default: 0.01)')
    p.set_defaults(minconf=0.01)
    
    p.add_option('-x', '--cutoff', dest='cutoff', type='int',
         help='Cutoff value for breaking the testing set for continuous learning')
    p.set_defaults(cutoff=10000)
    
    options, args = p.parse_args()
    
    if len(args) < 2:
        p.error('must provide the path to a CSV file to read')

    input = open(args[0])
    test = open(args[1])
    
    try:
        timer()
        initial_training_set = csv.reader(input)
        testing_set = csv.reader(test)
        
        minsup = options.minsup
        minconf = options.minconf        
        cutoff = options.cutoff
        
        """ begin fufp-growth """
        print 'Beginning FUFP-growth'
        print 'Support threshold', minsup*100, '%'
        fufp_growth_init(initial_training_set, minsup, minconf, cutoff, testing_set)
        
    finally:
        input.close()
