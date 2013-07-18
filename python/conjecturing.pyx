'''
Created on May 27, 2013

@author: nvcleemp
'''

class node:
    
    def __init__(self):
        self.left = None
        self.right = None
        self.type = 0
        self.isCommutative = False
        self.content = ''
        self.depth = None
    
    def __str__(self):
        if self.type == 0:
            return self.content
        elif self.type == 1:
            return '({} {})'.format(self.content, str(self.left))
        else:
            return '({} {} {})'.format(str(self.left), self.content, str(self.right)) 
    
    def addChild(self, node):
        if self.left == None:
            self.left = node
            self.type = 1
        elif self.right == None:
            self.right = node
            self.type = 2
        else:
            assert False, 'At most two children per node'
            
    def removeChild(self):
        if self.right == None:
            n, self.left, self.type = self.left, None, 0
        else:
            n, self.right, self.type = self.right, None, 1
        return n
    
    def setContent(self, content):
        self.content = content
    
    def getOrderedNodes(self):
        #maybe optimise by not constantly creating lists, but by supplying one list and appending to that
        if self.type == 2:
            return self.left.getOrderedNodes() + self.right.getOrderedNodes() + [self]
        elif self.type == 1:
            return self.left.getOrderedNodes() + [self]
        else:
            return [self]

#create a tree
treeRoot = None

cdef int treeDepth = 0
cdef int treeUCount = 0
cdef int treeBCount = 0

unusedNodes = []
nodesAtDepth = {}

cdef int currentUnary = 0
cdef int currentBinary = 0
    
def initTree(int unary, int binary):
    global treeRoot
    global treeDepth
    global treeUCount
    global treeBCount
    global unusedNodes
    global nodesAtDepth
    global currentUnary
    global currentBinary
    
    treeRoot = node()
    treeRoot.depth = 0
    unusedNodes = [node() for _ in range(unary + 2*binary)]
    
    nodesAtDepth = {0: [treeRoot]}        
    
    treeDepth = 0
    treeUCount = 0
    treeBCount = 0
    
    currentUnary = unary
    currentBinary = binary
    
def isComplete():
    return currentUnary == treeUCount and currentBinary == treeBCount

def treeAddChild(parent):
    global treeDepth
    global treeUCount
    global treeBCount
    
    child = unusedNodes.pop()
    parent.addChild(child)
    child.depth = parent.depth + 1
    if child.depth > treeDepth: treeDepth = child.depth
    
    if parent.type == 2:
        treeUCount -= 1
        treeBCount += 1
    else:
        treeUCount += 1
        
    if child.depth in nodesAtDepth:
        nodesAtDepth[child.depth].append(child)
    else:
        nodesAtDepth[child.depth] = [child]

def treeRemoveChild(parent):
    global treeDepth
    global treeUCount
    global treeBCount
    
    child = parent.removeChild()
    unusedNodes.append(child)
    
    nodesAtDepth[child.depth].pop()
    #child2 = self.nodesAtDepth[child.depth].pop()
    #assert child == child2, "Should be the same"
    if not nodesAtDepth[child.depth]: treeDepth -= 1
    
    if parent.type == 1:
        treeUCount += 1
        treeBCount -= 1
    else:
        treeUCount -= 1
    
    
def generateTree(int unary, int binary):
    initTree(unary, binary)
    for _ in _generateTree():
        yield 1
    
def _generateTree():
    if treeUCount > currentUnary + 1 or treeBCount > currentBinary:
        return
    
    if isComplete():
        yield 1
        return
    
    if treeDepth == 0:
        treeAddChild(treeRoot)
        for _ in _generateTree():
            yield 1
        treeRemoveChild(treeRoot)
    else:
        #get extensible nodes at level depth - 1
        start = len(nodesAtDepth[treeDepth-1]) - 1
        while start >= 0 and nodesAtDepth[treeDepth-1][start].type == 0:
            start -= 1
        
        if start >= 0 and nodesAtDepth[treeDepth-1][start].type == 1:
            start -= 1
            
        for parent in nodesAtDepth[treeDepth-1][start+1:]:
            treeAddChild(parent)
            for _ in _generateTree():
                yield 1
            treeRemoveChild(parent)
        
        
        #get extensible (i.e. all) nodes at level depth
        for parent in nodesAtDepth[treeDepth]:
            treeAddChild(parent)
            for _ in _generateTree():
                yield 1
            treeRemoveChild(parent)
        
def generateLabeledTree(unary, binary, invariantCount, unaryOperators, binaryNonCommutativeOperators, binaryCommutativeOperators):
    invariants = {'I{}'.format(i):True for i in range(1, invariantCount+1)}
    for _ in generateTree(unary, binary):
        nodes = treeRoot.getOrderedNodes()
        for _ in _generateLabeledTree(nodes, 0, invariants, unaryOperators, binaryNonCommutativeOperators, binaryCommutativeOperators):
            yield 1

def _generateLabeledTree(nodes, pos, invariants, unaryOperators, binaryNonCommutativeOperators, binaryCommutativeOperators):
    if pos == len(nodes):
        yield None #probably not good style, but sufficient for now
        return
    else:
        #label the node on position pos
        if nodes[pos].type == 0:
            for invariant in invariants:
                if invariants[invariant]:
                    nodes[pos].content = invariant
                    invariants[invariant] = False
                    for _ in _generateLabeledTree(nodes, pos + 1, invariants, unaryOperators, binaryNonCommutativeOperators, binaryCommutativeOperators):
                        yield None
                    invariants[invariant] = True
        elif nodes[pos].type == 1:
            for op in unaryOperators:
                nodes[pos].content = op
                for _ in _generateLabeledTree(nodes, pos + 1, invariants, unaryOperators, binaryNonCommutativeOperators, binaryCommutativeOperators):
                    yield None
        else:
            #non commutative operators
            for op in binaryNonCommutativeOperators:
                nodes[pos].content = op
                for _ in _generateLabeledTree(nodes, pos + 1, invariants, unaryOperators, binaryNonCommutativeOperators, binaryCommutativeOperators):
                    yield None
                
            
            #commutative operators
            for op in binaryCommutativeOperators:
                if str(nodes[pos].left) < str(nodes[pos].right):
                    nodes[pos].content = op
                    for _ in _generateLabeledTree(nodes, pos + 1, invariants, unaryOperators, binaryNonCommutativeOperators, binaryCommutativeOperators):
                        yield None
