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

class tree:
    
    def __init__(self, unary, binary):
        self.root = node()
        self.root.depth = 0
        self.unused = [node() for _ in range(unary + 2*binary)]
        
        self.nodesAtDepth = {0: [self.root]}        
        
        self.depth = 0
        self.uCount = 0
        self.bCount = 0
        
        self.unary = unary
        self.binary = binary
    
    def isComplete(self):
        return self.unary == self.uCount and self.binary == self.bCount
    
    def getOrderedNodes(self):
        return self.root.getOrderedNodes()
    
    def addChild(self, parent):
        child = self.unused.pop()
        parent.addChild(child)
        child.depth = parent.depth + 1
        if child.depth > self.depth: self.depth = child.depth
        
        if parent.type == 2:
            self.uCount -= 1
            self.bCount += 1
        else:
            self.uCount += 1
            
        if child.depth in self.nodesAtDepth:
            self.nodesAtDepth[child.depth].append(child)
        else:
            self.nodesAtDepth[child.depth] = [child]
    
    def removeChild(self, parent):
        child = parent.removeChild()
        self.unused.append(child)
        
        self.nodesAtDepth[child.depth].pop()
        #child2 = self.nodesAtDepth[child.depth].pop()
        #assert child == child2, "Should be the same"
        if not self.nodesAtDepth[child.depth]: self.depth -= 1
        
        if parent.type == 1:
            self.uCount += 1
            self.bCount -= 1
        else:
            self.uCount -= 1
    
    
def generateTree(unary, binary):
    for t in _generateTree(tree(unary, binary)):
        yield t
    
def _generateTree(t):
    if t.uCount > t.unary + 1 or t.bCount > t.binary:
        return
    
    if t.isComplete():
        yield t
        return
    
    if t.depth == 0:
        t.addChild(t.root)
        for nt in _generateTree(t):
            yield nt
        t.removeChild(t.root)
    else:
        #get extensible nodes at level depth - 1
        start = len(t.nodesAtDepth[t.depth-1]) - 1
        while start >= 0 and t.nodesAtDepth[t.depth-1][start].type == 0:
            start -= 1
        
        if start >= 0 and t.nodesAtDepth[t.depth-1][start].type == 1:
            start -= 1
            
        for parent in t.nodesAtDepth[t.depth-1][start+1:]:
            t.addChild(parent)
            for nt in _generateTree(t):
                yield nt
            t.removeChild(parent)
        
        
        #get extensible (i.e. all) nodes at level depth
        for parent in t.nodesAtDepth[t.depth]:
            t.addChild(parent)
            for nt in _generateTree(t):
                yield nt
            t.removeChild(parent)
        
def generateLabeledTree(unary, binary, invariantCount, unaryOperators, binaryNonCommutativeOperators, binaryCommutativeOperators):
    invariants = {'I{}'.format(i):True for i in range(1, invariantCount+1)}
    for t in generateTree(unary, binary):
        nodes = t.getOrderedNodes()
        for _ in _generateLabeledTree(nodes, 0, invariants, unaryOperators, binaryNonCommutativeOperators, binaryCommutativeOperators):
            yield t

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
