# A simple class for NFA/DFA States


# Note: No need to change this class for instantiating fresh/unique or named states
class State:
    """A class for states that can be optionally keyed on a value"""
    def __init__(self, name = None):
        """The default argument name==None constructs a new, unique, anonymous state"""
        self.name = name
    def __eq__(self, other):
        """Structural equality defers to self.name or to physical equality when name==None"""
        if self.name == None or other.name == None:
            return self is other
        else:
            return self.name == other.name
    def __hash__(self):
        """"Two __eq__ values must share a hash."""
        if self.name == None:
            return id(self)
        else:
            return hash(self.name)

        
