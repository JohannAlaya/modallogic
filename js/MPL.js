/**
 * MPL v1.3.2
 * (http://github.com/rkirsling/modallogic)
 *
 * A library for parsing and evaluating well-formed formulas (wffs) of modal propositional logic.
 *
 * Copyright (c) 2013-2015 Ross Kirsling
 * Released under the MIT License.
 */
var MPL = (function (FormulaParser) {
  'use strict';

  // begin formula-parser setup
  if (typeof FormulaParser === 'undefined') throw new Error('MPL could not find dependency: formula-parser');

  var variableKey = 'prop';
  
  var unaries = [
    { symbol: '~',  key: 'neg',  precedence: 6 },
    { symbol: '[]', key: 'nec',  precedence: 6 },
    { symbol: '<>', key: 'poss', precedence: 6 }
  ];

  var binaries = [
    { symbol: '&',   key: 'conj', precedence: 5, associativity: 'right' },
    { symbol: '|',   key: 'disj', precedence: 4, associativity: 'right' },
    { symbol: '->',  key: 'impl', precedence: 3, associativity: 'right' },
    { symbol: '<->', key: 'equi', precedence: 2, associativity: 'right' },
    { symbol: '?', key: 'know', precedence: 2, associativity: 'right' },
    { symbol: ',', key: 'group', precedence: 1, associativity: 'right' },
    { symbol: '#', key: 'eknow', precedence: 0, associativity: 'right' },
    { symbol: '/', key: 'distrib', precedence: 0, associativity: 'right'},
    { symbol: '§', key: 'common', precedence: 0, associativity: 'right'}
  ];

  var MPLParser = new FormulaParser(variableKey, unaries, binaries);
  // end formula-parser setup

  /**
   * Converts an MPL wff from ASCII to JSON.
   * @private
   */
  function _asciiToJSON(ascii) {
    return MPLParser.parse(ascii);
  }

  /**
   * Converts an MPL wff from JSON to ASCII.
   * @private
   */
  function _jsonToASCII(json) {
    if (json.prop)
      return json.prop;
    else if (json.neg)
      return '~' + _jsonToASCII(json.neg);
    else if (json.nec)
      return '[]' + _jsonToASCII(json.nec);
    else if (json.poss)
      return '<>' + _jsonToASCII(json.poss);
    else if (json.conj && json.conj.length === 2)
      return '(' + _jsonToASCII(json.conj[0]) + ' & ' + _jsonToASCII(json.conj[1]) + ')';
    else if (json.disj && json.disj.length === 2)
      return '(' + _jsonToASCII(json.disj[0]) + ' | ' + _jsonToASCII(json.disj[1]) + ')';
    else if (json.impl && json.impl.length === 2)
      return '(' + _jsonToASCII(json.impl[0]) + ' -> ' + _jsonToASCII(json.impl[1]) + ')';
    else if (json.equi && json.equi.length === 2)
      return '(' + _jsonToASCII(json.equi[0]) + ' <-> ' + _jsonToASCII(json.equi[1]) + ')';
    else if (json.know && json.know.length === 2)
      return '(' + _jsonToASCII(json.know[0]) + ' ? ' + _jsonToASCII(json.know[1]) + ')';
    else if (json.group && json.group.length === 2) {
      return _jsonToASCII(json.group[0]) + ' , ' + _jsonToASCII(json.group[1]);
    }
    else if (json.eknow && json.eknow.length === 2) {
      return '(' + _jsonToASCII(json.eknow[0]) + ' # ' + _jsonToASCII(json.eknow[1]) + ')';
    }
    else if (json.distrib && json.distrib.length === 2) {
      return '(' + _jsonToASCII(json.distrib[0]) + ' / ' + _jsonToASCII(json.distrib[1]) + ')';
    }
    else if (json.common && json.common.length === 2) {
      return '(' + _jsonToASCII(json.common[0]) + ' § ' + _jsonToASCII(json.common[1]) + ')';
    }
    else
      throw new Error('Invalid JSON for formula!');
  }

  /**
   * Converts an MPL wff from ASCII to LaTeX.
   * @private
   */
  function _asciiToLaTeX(ascii) {
    return ascii.replace(/~/g,      '\\lnot{}')
                .replace(/\[\]/g,   '\\Box{}')
                .replace(/<>/g,     '\\Diamond{}')
                .replace(/ & /g,    '\\land{}')
                .replace(/ \| /g,   '\\lor{}')
                .replace(/ <-> /g,  '\\leftrightarrow{}')
                .replace(/ -> /g,   '\\rightarrow{}');
  }

  /**
   * Converts an MPL wff from ASCII to Unicode.
   * @private
   */
  function _asciiToUnicode(ascii) {
    return ascii.replace(/~/g,    '\u00ac')
                .replace(/\[\]/g, '\u25a1')
                .replace(/<>/g,   '\u25ca')
                .replace(/&/g,    '\u2227')
                .replace(/\|/g,   '\u2228')
                .replace(/<->/g,  '\u2194')
                .replace(/->/g,   '\u2192');
  }

  /**
   * Constructor for MPL wff. Takes either ASCII or JSON representation as input.
   * @constructor
   */
  function Wff(asciiOrJSON) {
    // Strings for the four representations: ASCII, JSON, LaTeX, and Unicode.
    var _ascii = '', _json = '', _latex = '', _unicode = '';

    /**
     * Returns the ASCII representation of an MPL wff.
     */
    this.ascii = function () {
      return _ascii;
    };

    /**
     * Returns the JSON representation of an MPL wff.
     */
    this.json = function () {
      return _json;
    };

    /**
     * Returns the LaTeX representation of an MPL wff.
     */
    this.latex = function () {
      return _latex;
    };

    /**
     * Returns the Unicode representation of an MPL wff.
     */
    this.unicode = function () {
      return _unicode;
    };

    _json    = (typeof asciiOrJSON === 'object') ? asciiOrJSON : _asciiToJSON(asciiOrJSON);
    _ascii   = _jsonToASCII(_json);
    _latex   = _asciiToLaTeX(_ascii);
    _unicode = _asciiToUnicode(_ascii);
  }

  /**
   * Constructor for Kripke model. Takes no initial input.
   * @constructor
   */
  function Model() {
    // Array of states (worlds) in model.
    // Each state is an object with two properties:
    // - assignment: a truth assignment (in which only true values are actually stored)
    // - successors: an array of successor state indices for each agent (in lieu of a separate accessibility relation)
    // ex: [{assignment: {},          successors: {'a': [0,1]}},
    //      {assignment: {'p': true}, successors: {}   }]
    var _states = [];

    /**
     * Adds a transition to the model, given source and target state indices and corresponding agent.
     */
    this.addTransition = function (source, target, agentList) {
      if (!_states[source] || !_states[target]) return;

      var s = _states[source].successors;
      agentList.forEach(function (agent){
        if (s.has(agent)){
          var L = s.get(agent);
          L.push(target);
          s.set(agent, L);
        }
        else s.set(agent, [target]);
      })
    };

    /**
     * Removes a transition from the model, given source, target state indices and corresponding agent.
     */
    this.removeTransition = function (source, target, agentList) {
      if (!_states[source]) return;

      var s = _states[source].successors;
      agentList.forEach(function (agent){
        if (s.has(agent)){
          var L = s.get(agent);
          var index = L.indexOf(target);
          if (index !== -1) L.splice(index, 1);
         s.set(agent,L);
        }
      })
    };

    /**
     * Returns an array of successor states for a given state index and corresponding agent.
     */
    this.getSuccessorsOf = function (source,agent) {
      if (!_states[source]) return undefined;
      return _states[source].successors.get(agent);
    };

    this.getSuccessorsOfOld = function (source) {
      if (!_states[source]) return undefined;

      return _states[source].successors.values();
    };

    this.getAgents= function (source) {
      if (!_states[source]) return;

      return _states[source].successors.keys();
    }

    this.getAllAgents= function(){
      var L = [];
      _states.forEach(function (state) {
        if (state) {
          var g = state.successors
          g.forEach (function (value, key, map) {
            if (L.indexOf(key) === -1) { L.push(key);}
          })
        }
      })
      return L;
    }

    /**
     * Adds a state with a given assignment to the model.
     */
    this.addState = function (assignment) {
      var processedAssignment = {};
      for (var propvar in assignment)
        if (assignment[propvar] === true)
          processedAssignment[propvar] = assignment[propvar];

      _states.push({assignment: processedAssignment, successors: new Map([])}); /*changed successors type from list to map*/
    };

    /**
     * Edits the assignment of a state in the model, given a state index and a new partial assignment.
     */
    this.editState = function (state, assignment) {
      if (!_states[state]) return;

      var stateAssignment = _states[state].assignment;
      for (var propvar in assignment)
        if (assignment[propvar] === true) stateAssignment[propvar] = true;
        else if (assignment[propvar] === false) delete stateAssignment[propvar];
    };

    /**
     * Removes a state and all related transitions from the model, given a state index.
     */
    this.removeState = function (state) {
      if (!_states[state]) return;
      var self = this;

      _states[state] = null;
      _states.forEach(function (source, index, agent) {
        if (source) self.removeTransition(index, state, agent);
      });
    };

    /**
     * Returns an array containing the assignment (or null) of each state in the model.
     * (Only true propositional variables are returned in each assignment.)
     */
    this.getStates = function () {
      var stateList = [];
      _states.forEach(function (state) {
        if (state) stateList.push(state.assignment);
        else stateList.push(null);
      });

      return stateList;
    };

    this.getAllSuccessorsOf= function(state, agent) {
      var V = [];
      var C = model.getSuccessorsOf(state, agent);
      if(typeof C !== "undefined"){
        C=Array.from(C); //On fait un shallow copy de C
        while(C[0]){
          var s = C[0];
          if (!V.includes(s)){
            var L = model.getSuccessorsOf(s, agent);
            if(L !== undefined){
              L.forEach(function (x) {C.push(x);})
            }
            V.push(s);
          }
          C.shift();
        }
     }
      return V;
    }

    this.gAccessibility= function(state, list) {
      var S = [];
      var F = [];
      list.forEach(function (agent){
        S.push(model.getAllSuccessorsOf(state, agent.prop));
      });
      S.forEach(function (array){
        array.forEach(function (s) {
          if(F.indexOf(s) === -1) {
            F.push(s);
          }
        })
      })
      return F;
    }

    this.gAccessStrict= function(state, list) {
      var S = [];
      list.forEach(function (agent){
        S.push(model.getAllSuccessorsOf(state, agent.prop));
      });
      var F = S[0];
      S.forEach(function (array){
        F = F.filter(s => array.includes(s)); //intersection de S[0] et de des chemins de tous les autres agents
      })
      return F;
    }

    /**
     * Returns the truth value of a given propositional variable at a given state index.
     */
    this.valuation = function (propvar, state) {
      if (!_states[state]) throw new Error('State ' + state + ' not found!');

      return !!_states[state].assignment[propvar];
    };

    /**
     * Returns current model as a compact string suitable for use as a URL parameter.
     * ex: [{assignment: {'q': true}, successors: {'a' : [0,2]}}, null, {assignment: {}, successors: {}}]
     *     compresses to 'AqSa0,2;;AS;'
     */
    this.getModelString = function () {
      var modelString = '';

      _states.forEach(function (state) {
        if (state) {
          modelString += 'A' + Object.keys(state.assignment).join();
          modelString += 'S';
          if (state.successors !== {}){
            for (var agent in state.successors) {
              modelString += agent + state.successors[agent].join();
            }
          }
        }
        modelString += ';';
      });

      return modelString;
    };

    /**
     * Restores a model from a given model string.
     
     Cette partie n'a pas été adaptée aux fonctionalités de logique épistémique par manque de temps. */
    this.loadFromModelString = function (modelString) {
      var regex = /^(?:;|(?:A|A(?:\w+,)*\w+)(?:S|S(?:\d+,)*\d+);)+$/;
      if (!regex.test(modelString)) return;

      _states = [];

      var self = this,
          successorLists = [],
          inputStates = modelString.split(';').slice(0, -1);

      // restore states
      inputStates.forEach(function (state) {
        if (!state) {
          _states.push(null);
          successorLists.push(null);
          return;
        }

        var stateProperties = state.match(/A(.*)S(.*)/).slice(1, 3)
                                   .map(function (substr) { return (substr ? substr.split(',') : []); });

        var assignment = {};
        stateProperties[0].forEach(function (propvar) { assignment[propvar] = true; });
        _states.push({assignment: assignment, successors: {}});

        var successors = stateProperties[1].map(function (succState) { return +succState; });
        successorLists.push(successors);
      });

      // restore transitions
      successorLists.forEach(function (successors, source) {
        if (!successors) return;
        successors.forEach(function (target) {
          self.addTransition(source, target, agent);
        });
      });
    };
  }

  /**
   * Evaluate the truth of an MPL wff (in JSON representation) at a given state within a given model.
   * @private
   */

  function _truth(model, state, json) {
    if (json.prop)
      return model.valuation(json.prop, state);
    else if (json.neg)
      return !_truth(model, state, json.neg);
    else if (json.conj)
      return (_truth(model, state, json.conj[0]) && _truth(model, state, json.conj[1]));
    else if (json.disj)
      return (_truth(model, state, json.disj[0]) || _truth(model, state, json.disj[1]));
    else if (json.impl)
      return (!_truth(model, state, json.impl[0]) || _truth(model, state, json.impl[1]));
    else if (json.equi)
      return (_truth(model, state, json.equi[0]) === _truth(model, state, json.equi[1]));
    else if (json.nec) {
      var L = Array.from(model.getSuccessorsOfOld(state));
      if (L.length === 0) return true;
      else return L[0].every(function (succState) { return _truth(model, succState, json.nec); }); 
      //ici L est un array qui contient un array, donc je passe par L[0]. Ce comportement semble issu de l'utilisation de Array.from, mais sans passer par la, le résultat de getSuccessorsOfOld n'est pas iterable.
    }
    else if (json.poss){
      var L = Array.from(model.getSuccessorsOfOld(state));
      if (L.length === 0) return true;
      else return L[0].some(function (succState) { return _truth(model, succState, json.poss); });
    }
    else if (json.know){
      var A = model.getSuccessorsOf(state, json.know[0].prop);
      if (typeof A === "undefined"){ return true;}
      else return A.every(function (succState) { return _truth(model, succState, json.know[1]); });
    }
    else if (json.group){
      var g = json.group;
      var a;
      var L = [];
      while(g){
        a = g[0];
        if(L.indexOf(a) === -1) {L.push(a);}
        if(g[1].prop) {L.push(g[1])};
        g=g[1].group;
      }
      return L;
    }
    else if (json.eknow){
      var L = _truth(model, state, json.eknow[0]);
      if (L instanceof Array) {
        return L.every(function (agent) { var a = {know: [agent, json.eknow[1]]}; return _truth(model, state, a);});
      }
      else return undefined;
    }
    else if (json.distrib){
      var L = _truth(model, state, json.distrib[0]);
      if (L instanceof Array) {
        var A = model.gAccessStrict(state, L);
        return A.every(function (state) {return _truth(model, state, json.distrib[1]);});
       //var A = [];
       //L.forEach(function (agent) {A.push(model.getSuccessorsOf(state, agent.prop));});
       //console.log(A);
       //if (A.includes(undefined)) {var B = undefined;}
       //else {var B = A[0];
        //A.forEach(function (array) {B.filter(x => array.includes(x));});}
       //if (B === undefined) {return true;}
       //else {return B.every(function (state) {return _truth(model, state, json.distrib[1]);});}
      }
      else return undefined;
    }
    else if (json.common){
      var L = _truth(model, state, json.common[0]);
      if (L instanceof Array) {
        var G = model.gAccessibility(state, L);
        return G.every(function (s) {return _truth(model, s, json.common[1]);});
      }
      else return undefined;
    }
    else
      throw new Error('Invalid formula!');
  }

  /**
   * Evaluate the truth of an MPL wff at a given state within a given model.
   */
  function truth(model, state, wff) {
    if (!(model instanceof MPL.Model)) throw new Error('Invalid model!');
    if (!model.getStates()[state]) throw new Error('State ' + state + ' not found!');
    if (!(wff instanceof MPL.Wff)) throw new Error('Invalid wff!');

    return _truth(model, state, wff.json());
  }

  // export public methods
  return {
    Wff: Wff,
    Model: Model,
    truth: truth
  };

})(FormulaParser);
