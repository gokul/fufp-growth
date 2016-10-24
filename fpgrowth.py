# encoding: utf-8

"""
A Python implementation of the FP-growth algorithm.
B. GOkulakrishnan
"""

from collections import defaultdict, namedtuple
from itertools import chain, combinations, imap

from FPTree import FPTree
from FPNode import FPNode

freqTable = dict()

ctr = 0
timeList = []
import time

def timer():
    global timeList
    timeList.append(time.time())
    if len(timeList)%2 == 0:
        print 'Time elapsed: ' + str(round(timeList[-1] - timeList[-2],4)) + ' s.'
        timeList.pop()
        timeList.pop()

def find_frequent_itemsets(transactions, minimumSupport, include_support=False):
    """
    Find frequent itemsets in the given transactions using FP-growth.
    
    This method uses the FP-tree to represent the transactions and mines them
    based on the provided minimum support.
    
    returns a list of frequent itemsets from the provided comma separated database.
    
    """
    items = defaultdict(lambda: 0) # mapping from items to their supports
    processed_transactions = []
    
    print '\nFP-tree construction'
    # Load the passed-in transactions and count the support that individual
    # items have.

    le = 1
    global ctr
    for transaction in transactions:
        processed = []
        for item in transaction:
            items[item] += 1
            processed.append(item)
        processed_transactions.append(processed)
        
        if len(transaction)>le:
            le = len(transaction)
            ctr += 1
            
              
    minimum_support = int(len(processed_transactions)*float(minimumSupport/100))
    
    """ Remove infrequent items from the item support dictionary."""
    items = dict((item, support) for item, support in items.iteritems()
        if support >= minimum_support)

    """ 
    Build the FP-tree. Before any transactions can be added to the tree, they
    must be stripped of infrequent items and their surviving items must be
    sorted in decreasing order of frequency.
    """
    def clean_transaction(transaction):
        transaction = filter(lambda v: v in items, transaction)
        transaction.sort(key=lambda v: items[v], reverse=True)
        return transaction

    master = FPTree()
    for transaction in imap(clean_transaction, processed_transactions):
        master.add(transaction)
        
        """"master = completed FP-tree for the OLD DB"""

    def find_with_suffix(tree, suffix):
        
        for item, nodes in tree.items():
            support = sum(n.count for n in nodes)
            if support >= minimum_support and item not in suffix:
                """ New winner!"""                
                found_set = [item] + suffix
                freqTable[frozenset(found_set)] = support
                yield (found_set, support) if include_support else found_set
                
                """ Build a conditional tree and recursively search for frequent
                itemsets within it."""
                cond_tree = conditional_tree_from_paths(tree.prefix_paths(item),
                    minimum_support)
                for s in find_with_suffix(cond_tree, found_set):
                    yield s # pass along the good news to our caller

    """ Search for frequent itemsets, and yield the results we find."""
    
    final = []
    print 'FP-tree mining'
    for itemset in find_with_suffix(master, []):
        final.append(itemset)
    return final



def conditional_tree_from_paths(paths, minimum_support):
    """Builds a conditional FP-tree from the given prefix paths."""
    tree = FPTree()
    condition_item = None
    items = set()

    """"Import the nodes in the paths into the new tree. Only the counts of the
    leaf notes matter; the remaining counts will be reconstructed from the
    leaf counts."""
    for path in paths:
        if condition_item is None:
            condition_item = path[-1].item

        point = tree.root
        for node in path:
            next_point = point.search(node.item)
            if not next_point:
                """Add a new node to the tree."""
                items.add(node.item)
                count = node.count if node.item == condition_item else 0
                next_point = FPNode(tree, node.item, count)
                point.add(next_point)
                tree._update_route(next_point)
            point = next_point

    assert condition_item is not None

    """"Calculate the counts of the non-leaf nodes."""
    for path in tree.prefix_paths(condition_item):
        count = None
        for node in reversed(path):
            if count is not None:
                node._count += count
            count = node.count

    """"Eliminate the nodes for any items that are no longer frequent."""
    for item in items:
        support = sum(n.count for n in tree.nodes(item))
        if support < minimum_support:
            # Doesn't make the cut any more
            for node in tree.nodes(item):
                if node.parent is not None:
                    node.parent.remove(node)

    """"Finally, remove the nodes corresponding to the item for which this
    conditional tree was generated."""
    for node in tree.nodes(condition_item):
        if node.parent is not None: # the node might already be an orphan
            node.parent.remove(node)

    return tree

#===================================================================================== 
      
def generateRules(data, conf):
    """generate rules based on 'conf' from the data from 'data' """
    print 'Rule generation in progress'
    rulez = []
    holder = dict()
    counter = 0;
    def getSupport(pat):
        if not freqTable.has_key(pat):
            return -1
        support = freqTable[pat]
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
                if (itemSup < 0 or elemSup < 0): #avoid division by zero
                    continue
                confidence = itemSup /elemSup
                if confidence >= conf:
                    """new rule"""
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
    """ evaluate the generated rules from the actual data from the sessions """
    count+=1
    if actual in recommendationSet:
        average = calculateAccuracy(1,average,count)
        correct+=1
        return (average,count,correct)
    else:
        average=calculateAccuracy(0,average,count)
        return (average,count,correct)
    
def calculateAccuracy(correct,average,count):
    """returns the accuracy value"""
    return ((int(count)-1)*float(average)+int(correct))*100/int(count)

              
def recommend(session, holder):
    """ create recommendations based on the sessions in 'holder' """
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

def fpgrowthRecommender(sessions, holder):
    """ mother method for the recommendation module """
    file_iter = open(sessions, 'rU')
    count=0
    average=0
    total = 0
    correct =0
    print '\nBeginning prediction and evaluation'
    for line in file_iter:
        line = line.strip().rstrip(',')
        elem = line.split(',')
        iterator =0
        sessionList =[]
        if len(elem)>1:
            for item in elem:
                iterator +=1
                if iterator==(len(elem)-1):
                    break
                sessionList.append(item)
                recommendationList = recommend(sessionList, holder)
                total+=1
                if not (len(recommendationList)<1):
                    result= evaluate(recommendationList, elem[iterator], average, count,correct)
                    average=result[0] 
                    count=result[1] 
                    correct=result[2]
                    
    if not (count == 0 or total == 0):                
        accuracy = float(correct)/float(count)
        coverage = float(count)/float(total)
        #print "Average : ", average
        print "\nRequests for prediction : ",total
        print "Predictions made : ", count
        print "\nCorrect : ", correct
        print "\nAccuracy :  %.4f" % (accuracy*100)
        print "Coverage :  %.4f"  % (coverage*100)
        timer()

#=====================================================================================

if __name__ == '__main__':
    from optparse import OptionParser
    import csv

    p = OptionParser(usage='%prog data_file')
    
    p.add_option('-s', '--minimum-support', dest='minsup', type='float',
        help='Minimum itemset support (default: 0.1)')
    p.set_defaults(minsup=0.1)
    
    p.add_option('-c', '--minimum-confidence', dest='minconf', type='float',
         help='Minimum confidence threshold for association rules (default: 0.01)')
    p.set_defaults(minconf=0.01)
    
    options, args = p.parse_args()
    
    #if len(args) < 2:
     #   p.error('must provide the path to a CSV file to read')

    f = open(args[0])
    sessions = args[1]
    
    try:
        timer()
        print 'FP-growth started'
        print 'Support threshold:', options.minsup*100, '%'
        
        freq_pats = find_frequent_itemsets(csv.reader(f), options.minsup)
        
            
        ruleset, holder = generateRules(freqTable, options.minconf)
        
#===============================================================================
#        print '--------- Association rules ---------'
#        for result, confidence in ruleset:
# 
#            pre, post = result
#            print " %s ==> %s , %.4f" % (str(pre), str(post), confidence)
#===============================================================================

        fpgrowthRecommender(sessions, holder)

    finally:
        f.close()
