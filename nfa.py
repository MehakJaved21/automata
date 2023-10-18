#!/usr/bin/env python3
# -*- coding: utf-8 -*-


# I mehak javed have written all of this project myself, without any
# unauthorized assistance, and have followed the academic honor code.


from nfa_regex import *
from state import *
# Note: You may want to use the provided generateSVG() method below for visualizing,
# your NFAs/DFAs and for debugging. If not, you may remove it and the following import.
# You are not required to provide a working generateSVG method, but you may find it useful.
try:
	from graphviz import Digraph
except:
	pass



# TODO: This is your class for modeling NFAs/DFAs! Some is already stubbed out for you.
class NFA:
    def __init__(self, r=None):
        self.r = r
        if r is None:
            start = State()
            self.Q = {start}
            self.Sigma = set()
            self.s = start
            self.F = set()
            self.delta = set()
        elif isinstance(r, EpsilonRegex):
            start = State()
            end = State()
            self.Q = {start, end}
            self.Sigma = set()
            self.s = start
            self.F = {end}
            self.delta = {(start, "", end)}
        elif isinstance(r, StarRegex):
            nfa0 = NFA(r.r0)
            start = State()
            end = State()
            self.Q = nfa0.Q | {start, end}
            self.Sigma = nfa0.Sigma
            self.s = start
            self.F = {end}
            self.delta = nfa0.delta | {(start, "", nfa0.s), (nfa0.s, "", end), (end, "", start)}
        elif isinstance(r, SeqRegex):
            nfa0 = NFA(r.r0)
            nfa1 = NFA(r.r1)
            start = nfa0.s
            end = nfa1.F.pop()
            self.Q = nfa0.Q | nfa1.Q
            self.Sigma = nfa0.Sigma | nfa1.Sigma
            self.s = start
            self.F = {end}
            self.delta = nfa0.delta | nfa1.delta | {(nfa0.F.pop(), "", nfa1.s)}
        elif isinstance(r, DisjRegex):
            nfa0 = NFA(r.r0)
            nfa1 = NFA(r.r1)
            start = State()
            end = State()
            self.Q = nfa0.Q | nfa1.Q | {start, end}
            self.Sigma = nfa0.Sigma | nfa1.Sigma
            self.s = start
            self.F = {end}
            self.delta = nfa0.delta | nfa1.delta | {(start, "", nfa0.s), (start, "", nfa1.s), (nfa0.F.pop(), "", end), (nfa1.F.pop(), "", end)}
        elif isinstance(r, CharRegex):
            start = State()
            end = State()
            self.Q = {start, end}
            self.Sigma = {r.x}
            self.s = start
            self.F = {end}
            self.delta = {(start, r.x, end)}
        else:
            raise ValueError("NFA must be constructed from a Regex (or None).")


    def matches(self, s):
        # Note how move and epsilon closure (written correctly) may be used to
        # simulate an NFA or DFA (this code can work for both!)
        # See also: the nfa-dfa and subset algorithm slides from class for move, epsilonClosure.
        current = self.epsilonClosure({self.s})
        for x in s:
            current = self.epsilonClosure(self.move(current, x))
        if current & self.F == set():
            return False
        else:
            return True
        
        
    def epsilonClosure(self, qs):
        """Returns the set of states reachable from those in qs without consuming any characters."""
        closure = set(qs)
        stack = list(qs)
        while stack:
            q = stack.pop()
            for transition in self.delta:
                if transition[0] == q and transition[1] == "":
                    if transition[2] not in closure:
                        closure.add(transition[2])
                        stack.append(transition[2])
        return closure


    
    def move(self, qs, x):
        """Returns the set of states reachable from those in qs by consuming character x."""
        reachable_states = set()
        for state in qs:
            for transition in self.delta:
                if transition[0] == state and transition[1] == x:
                    reachable_states.add(transition[2])
        return reachable_states


    
    def NFA_to_DFA(self):
        dfa = NFA()  # Create a new NFA to represent the DFA
        dfa.r = self.r  # Set the same regex

        # Initialize the start state of the DFA
        startset = self.epsilonClosure({self.s})
        start = State(frozenset(startset))
        dfa.Q = {start}

        unmarked_states = [start]
        marked_states = set()

        while unmarked_states:
            current_state = unmarked_states.pop()
            marked_states.add(current_state)

            for symbol in self.Sigma:
                target_state = self.epsilonClosure(self.move(current_state.name, symbol))
                if not target_state:
                    continue

                new_state = State(frozenset(target_state))
                if new_state not in dfa.Q:
                    unmarked_states.append(new_state)
                    dfa.Q.add(new_state)
                dfa.delta.add((current_state.name, symbol, new_state.name))

                if new_state.name in self.F:
                    dfa.F.add(new_state)

        return dfa


    
    def statecount(self):
        return len(self.Q)
        
        
    def isDFA(self):
        # Checks to see if the NFA is also a DFA:
        # i.e., reports True iff self.delta is a function
        for q in self.Q:
            outgoingset = set()
            for e in self.delta:
                if q == e[0]:
                    if e[1] in outgoingset or e[1] == "":
                        return False
                    outgoingset.add(e[1])
        return True


    def minimizeDFA(self):
        if not self.isDFA():
            raise Exception("minimizeDFA must be provided a DFA")

        # Create a mapping of states to their corresponding partitions
        partition_map = {}
        accepting_states = set()
        non_accepting_states = set()

        for state in self.Q:
            if state in self.F:
                partition_map[state] = 'A'
                accepting_states.add(state)
            else:
                partition_map[state] = 'NA'
                non_accepting_states.add(state)

        # Create initial partitions
        P = [accepting_states, non_accepting_states]

        # Initialize the new DFA
        mdfa = NFA()
        mdfa.r = self.r

        # Continue until no more partitions can be refined
        while True:
            new_partitions = []
            for part in P:
                for symbol in self.Sigma:
                    partitions = {}
                    for state in part:
                        target = self.move({state}, symbol)
                        partition = partition_map[list(target)[0]]
                        if partition in partitions:
                            partitions[partition].add(state)
                        else:
                            partitions[partition] = {state}
                    new_partitions.extend(partitions.values())

                    # Update transitions based on the new partitions
                    for key, value in partitions.items():
                        if len(value) > 1:
                            for s in value:
                                partition_map[s] = key

            if new_partitions:
                P = new_partitions
            else:
                break

        # Set the new states and transitions for the minimized DFA
        mdfa.Q = {State(frozenset(part)) for part in P}
        mdfa.F = {state for state in mdfa.Q if state in accepting_states}

        for from_state in self.Q:
            for symbol in self.Sigma:
                to_states = self.move({from_state}, symbol)
                mdfa.delta.add((partition_map[from_state], symbol, partition_map[list(to_states)[0]]))

        return mdfa


    # Note: You do not need to touch this function, but may, and may find it useful for
    # generating visualizations of the NFA/DFA for understanding and debugging purposes
    def generateSVG(self,file_name="nfa",title=True):
        """Writes the current NFA to a dot file and runs graphviz (must be locally installed!)"""

        # Setup
        dot = Digraph(name='nfa',comment='nfa')
        dot.attr(rankdir='LR')
        names = {}
        if title == True:
            dot.node("regex",label='<<FONT POINT-SIZE="24">'+str(self.r)+'</FONT>>', shape="square", style="rounded", height="0", width="0", margin="0.05")
        elif isinstance(title,str):
            dot.node("regex",label='<<FONT POINT-SIZE="24">'+title+'</FONT>>', shape="square", style="rounded", height="0", width="0", margin="0.05")
        dot.node("*", style="invis", height="0", width="0", margin="0")
        
        def pad_lab(s):
            """For some reason graphviz needs spaces padding this to render right."""
            return "  "+s+"  "
        def str_lab(s):
            if s == "": return "ε"
            else: return str(s)

        # Nodes and Edges
        def namer(n): return "<q<sub><font point-size=\"11\">"+n+"</font></sub>>"
        if self.s in self.F:
            dot.node(str(len(names)),namer(str(len(names))), shape="doublecircle")
        else:
            dot.node(str(len(names)),namer(str(len(names))), shape="circle")
        names[self.s] = len(names)
        for n in (self.Q - self.F - {self.s}):
            dot.node(str(len(names)),namer(str(len(names))), shape="circle")
            names[n] = len(names)
        for n in (self.F - {self.s}):
            dot.node(str(len(names)),namer(str(len(names))), shape="doublecircle")
            names[n] = len(names)
        pseudodelta = dict()
        for e in self.delta:
            if (e[0],e[2]) in pseudodelta:
                pseudodelta[(e[0],e[2])] |= frozenset({e[1]})
            else:
                pseudodelta[(e[0],e[2])] = frozenset({e[1]})
        for k in pseudodelta.keys():
            dot.edge(str(names[k[0]]), str(names[k[1]]), label=pad_lab(
                ",".join(list(map(str_lab,sorted(list(pseudodelta[k])))))))
        dot.edge("*", str(names[self.s]), label="")

        dot.format = 'svg'
        dot.render(filename=file_name, cleanup=True)
