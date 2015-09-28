#!/usr/bin/env python
from collections import deque
'''
Verifies transformational proofs in George syntax.

Code is currently very ugly, it would be appreciated if people can help clean/bugfix.
'''

'''
Copyright (c) 2015 Filip Burlacu

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
''' 

# parse a string containing just the Transformational Proof

proof = """
! (r => ! ((p | r) & (r | q))) <->  r
%% blink
1) ! (r => ! ((p | r) & (r | q))) %% waggle
2) ! (r => ! ((r | p) & (r | q))) by comm
3) ! (r => ! (r | (p & q))) by distr
4) !(! r | ! (r | (p & q))) by impl
%% snout
5) !(! r | ! r & ! (p & q)) by dm 
6) !!r by simp2
7) r by neg
"""

precedence = { # all ops are right-associative
        '=' : 1,
        '>' : 2,
        '|' : 3,
        '&' : 4,
        '!' : 5, # highest precedence, simple as that
}
ops = set(precedence.keys())

def tokenize(s):
    '''
    tokenize an expression
    '''
    # Woefully inefficient multi-pass design, but it's simple and it works
    # We'd use re if we were doing giant lines, obv
    s = s.replace('(', ' ( ')
    s = s.replace(')', ' ) ')
    s = s.replace('|', ' | ')
    s = s.replace('&', ' & ')
    s = s.replace('!', ' ! ')
    s = s.replace('<=>', ' = ') # note the change of symbol
    s = s.replace('=>', ' > ')  # so all operators

    s = s.split() # s is now tokenized!
    return s

def lex(proof):
    proof = proof.split("\n")
    for i in xrange(len(proof)):
        proof[i] = proof[i].split("%")[0] # remove comments before removing empty lines
    proof = filter(lambda s: s != "", proof) # remove empty lines

    proof[0] = proof[0].split('<->')

    # remove labels in front of proof lines:
    proof[1:] = (s.split(')', 1)[-1] for s in proof[1:])
    proof[1] = [proof[1]] # listify
    proof[2:]= (s.split('by') for s in proof[2:]) # each line is now a pair [expr, rule]
    for a in proof:
        a[:] = (s.strip() for s in a)
        a[0] = tokenize(a[0])
    proof[0][1] = tokenize(proof[0][1]) # The only expr left out by above loop

    # And now we rearrange it for easier interpretation:
    proof[1].append('premise')
    temp = zip(*proof[1:])
    out = {'target' : proof[0], 'steps' : temp[0], 'rules' : temp[1]}
    return out

def prefix(s):
    '''
    Does the shunting-yarding of a tokenized expr, returning the prefix-notation form
    '''
    out = []
    stack = []
    s = deque(s)

    while s:
        tok = s.popleft()
        if tok.isalpha():
            out.append(tok)
            continue
        if tok is '(':
            stack.append(tok)
            continue
        if tok in ops:
            while stack and stack[-1] in ops and precedence[tok] < precedence[stack[-1]]:
                out.append(stack.pop())
            stack.append(tok)
        if tok is ')':
            while stack and stack[-1] != '(':
                out.append(stack.pop())
            if not stack:
                print "MISHMASHED PARENTS"
                return False
            stack.pop() # pop '('
    while stack:
        tok = stack.pop()
        if tok is '(':
            print "MISHMASHED PARENTS"
            return False
        out.append(tok)
    out.reverse() # because it makes a world of difference
    return out

def diffPN(t1,t2):
    'Return the first differing index of two trees in prefix notation'
    for i in xrange(len(t1)):
        if t1[i] != t2[i]: return i
    return -1

def childPN(parent, i):
    'returns the child tree starting at the specified index of a prefix tree'
    count = 1
    for j in xrange(i, len(parent)):
        tok = parent[j]
        if tok is '!':
            count += 0
        elif tok in '&|>=':
            count += 1
        else:
            count -= 1
        if count == 0:
            return [e for e in parent[i:j+1]]
    raise "Bad Syntax, Cannot get child"

'''
Basic method for testing if a rule was applied correctly:

- Diff the two expressions, grab the differing subtrees
- With these two subtrees, pattern-match the first and second layers of children
    against the listed rule
'''

def testRule(t1, t2, rule):
    i = diffPN(t1, t2)
    op0 = t1[i - 1]
    c11 = childPN(t1, i)
    c21 = childPN(t2, i)
    c12 = childPN(t1, i + len(c11))
    c22 = childPN(t2, i + len(c21))

    # Now to choose the rule:
    if rule is "comm":
        print t1, t2
        print op0
        print c11, c12, c21, c22
        return op0 in '&|=' and diffPN(c11, c22) == -1 and diffPN(c12, c21) == -1






proof = lex(proof)
'''
print proof['target']
for i in proof['steps']:
    r = prefix(i)
    print " ".join(i) + " ~~ " + " ".join(r)
print proof['rules']'''
#print RPN(proof['steps'][0])
print " ".join(proof['steps'][0])
pn = prefix(proof['steps'][0])
for i in xrange(len(pn)):
    print childPN(pn, i)


test1 = prefix(tokenize("a & b"))
test2 = prefix(tokenize("b & a"))

print testRule(test1, test2, "comm")
