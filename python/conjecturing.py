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
            return n
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
        
        self.nodesAtDepth = {0: self.root}        
        
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
    
    
def generateTree(unary, binary):
    for t in _generateTree(tree(unary, binary)):
        yield t
    
def _generateTree(t):
    if t.isComplete():
        yield t
        return
    
    if t.depth == 0:
        t.uCount += 1
        t.addChild(t.root)
        t.depth = 1
        for nt in _generateTree(t):
            yield nt
        t.depth = 0
        t.removeChild(t.root)
        t.uCount -= 1
    else:
        #get extensible nodes at level depth - 1
        #get extensible (i.e. all) nodes at level depth
        
        pass
        
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
            
            #commutative operators
            pass
                                
        
