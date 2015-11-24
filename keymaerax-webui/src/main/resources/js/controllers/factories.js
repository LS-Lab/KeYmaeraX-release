/* Factory to create a model (as in MVC) for exchanging KeYmaera X models between controllers */
angular.module('keymaerax.controllers').factory('Models', function () {
    var models = [];

    return {
        getModels: function() {
            return models;
        },
        setModels: function(m) {
            models = m;
        },
        addModel: function(model) {
            models.push(model);
        },
        addModels: function(m) {
            for (var i = 0; i < m.length; i++) {
                models.push(m[i]);
            }
        }
    };
});

/* Factory to create a model (as in MVC) for exchanging a KeYmaera X proof agenda between controllers */
angular.module('keymaerax.controllers').factory('Agenda', function () {

    /**
     * tasks is a list of { $hashKey, nodeId = "_0_0...", proofId = hash, proofNode = {sequent, children ...} }
     */
    var tasks = [];
    /**
     * a task looks like { $hashKey, nodeId = "_0_0...", proofId = hash, proofNode = {sequent, children ...} }
     */
    var selectedTask;

    return {
        getTasks: function() {
            return tasks;
        },
        setTasks: function(t) {
            tasks = t;
        },
        addTask: function(task) {
            tasks.push(task);
        },
        addTasks: function(t) {
            for (var i = 0; i < t.length; i++) {
                tasks.push(t[i]);
            }
        },
        getSelectedTask: function() {
            return selectedTask;
        },
        setSelectedTask: function(t) {
            selectedTask.selected = false;
            selectedTask = t;
            t.selected = true;
        }
    };
});

angular.module('keymaerax.controllers').factory('Tactics', function ($rootScope) {
    var makeRuleLabel = function(name, top, bot) {
        return "\\(\\left(" + name + "  \\right) " + "\\frac{" + top + "}{" + bot + "}\\)";
    }

    var ruleTactics = {
        // TODO add rules, move into own file
        "dl.and-left" :
            { "name" : "dl.and-left",
              "label" : "\\(\\left(\\wedge l \\right) \\frac{\\Gamma, \\phi, \\psi ~\\vdash~ \\Delta}{\\Gamma,\\phi \\wedge \\psi ~\\vdash~ \\Delta}\\)"
            },
        "dl.and-right" :
            { "name" : "dl.and-right",
              "label" : "\\(\\left(\\wedge r \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta \\qquad \\Gamma ~\\vdash~ \\psi,\\Delta}{\\Gamma ~\\vdash~ \\phi \\wedge \\psi,\\Delta}\\)"
            },
        "dl.or-left" :
            { "name" : "dl.or-left",
              "label" : "\\(\\left(\\vee l \\right) \\frac{\\Gamma,\\phi ~\\vdash~ \\Delta \\qquad \\Gamma,\\psi ~\\vdash~ \\Delta}{\\Gamma \\phi \\vee \\psi ~\\vdash~ \\Delta}\\)"
            },
        "dl.or-right" :
            { "name" : "dl.or-right",
              "label" : "\\(\\left(\\vee r \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\psi,\\Delta}{\\Gamma ~\\vdash~ \\phi \\vee \\psi,\\Delta}\\)"
            },
        "dl.imply-left" :
            { "name" : "dl.imply-left",
              "label" : "\\(\\left(\\rightarrow l \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta \\qquad \\Gamma ~\\vdash~ \\psi,\\Delta}{\\Gamma \\phi \\rightarrow \\psi ~\\vdash~ \\Delta}\\)"
            },
        "dl.imply-right" :
            { "name" : "dl.imply-right",
              "label" : "\\(\\left(\\rightarrow r \\right) \\frac{\\Gamma, \\phi ~\\vdash~ \\psi,\\Delta}{\\Gamma ~\\vdash~ \\phi \\rightarrow \\psi,\\Delta}\\)"
            },
        "dl.equiv-left" :
            { "name" : "dl.equiv-left",
              "label" : "TODO: \\(\\leftrightarrow l\\)"
            },
        "dl.equiv-right" :
            { "name" : "dl.equiv-right",
              "label" : "TODO: \\(\\leftrightarrow r\\)"
            },
        "dl.not-left" :
            { "name" : "dl.not-left",
              "label" : "\\(\\left(\\neg l \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta}{\\Gamma,\\neg\\phi ~\\vdash~ \\Delta}\\)"
            },
        "dl.not-right" :
            { "name" : "dl.not-right",
              "label" : "\\(\\left(\\neg r \\right) \\frac{\\Gamma, \\phi ~\\vdash~ \\Delta}{\\Gamma ~\\vdash~ \\neg \\phi, \\Delta}\\)"
            },
        "dl.close-true" :
            { "name" : "dl.close-true",
              "label" : "\\(\\left(\\textit{true} r \\right) \\frac{}{\\Gamma ~\\vdash~ \\textit{true},\\Delta}\\)"
            },
        "dl.close-false" :
            { "name" : "dl.close-false",
              "label" : "\\(\\left(\\textit{true} r \\right) \\frac{}{\\Gamma, \\textit{false} ~\\vdash~ \\Delta}\\)"
            },
        "dl.skolemize" :
            { "name" : "dl.skolemize",
              "label" : "\\( \\left( \\forall r \\right) \\frac{\\Gamma ~\\vdash~ \\phi\\left(s\\left(X_1,\\ldots,X_n\\right)\\right)}{\\Gamma ~\\vdash~ \\forall x . \\phi(x), \\Delta} \\)"
            },
        "dl.decomposeQuan" :
            { "name" : "dl.decomposeQuan",
              "label" : "\\( \\left( \\textit{decompose} \\right) \\frac{(\\forall/\\exists) x_1. \\left( \\ldots (\\forall/\\exists) x_n . \\phi \\right)}{(\\forall/\\exists) \\vec{x} . \\phi } \\)"
            },
        "dl.box-assign" :
            { "name" : "dl.box-assign",
              "label" : "\\(\\left(\\left[:=\\right]\\right) \\frac{\\forall x. x = t \\to \\phi(x)}{\\left[x := t\\right]\\phi(x)}\\)"
            },
        "dl.box-choice" :
            { "name" : "dl.box-choice",
              "label" : "\\(\\left(\\left[\\cup\\right]\\right) \\frac{\\left[\\alpha\\right]\\phi \\qquad \\left[\\beta\\right]\\phi}{\\left[\\alpha \\cup \\beta\\right]\\phi}\\)"
            },
        "dl.box-induction" :
            { "name" : "dl.box-induction",
              "label" : "\\(\\left(\\left[\\alpha^*\\right] \\text{ind}\\right) \\frac{\\left(\\phi \\wedge \\left[\\alpha^*\\right]\\left(\\phi \\rightarrow \\left[\\alpha\\right] \\phi \\right)\\right) }{\\left[\\alpha^*\\right]\\phi}\\)"
            },
        "dl.induction" :
            { "name" : "dl.induction",
              "label" : "\\(\\left(\\left[\\alpha^*\\right] \\text{ind}\\right) \\frac{\\Gamma ~\\vdash~ \\phi, \\Delta \\quad \\Gamma ~\\vdash~ \\forall^\\alpha \\left(\\phi \\to \\left[\\alpha\\right]\\phi\\right) \\quad \\Gamma ~\\vdash~ \\forall^\\alpha \\left(\\phi \\to \\psi \\right)}{\\Gamma ~\\vdash~ \\left[\\alpha^*\\right]\\psi,\\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "\\(\\phi\\)", "placeholder" : "Invariant", "type" : "text" } ]
            },
        "dl.box-ndetassign" :
            { "name" : "dl.box-ndetassign",
              "label" : "\\(\\left(\\left[:= *\\right]\\right) \\frac{\\forall x. \\phi(x)}{\\left[x := *\\right]\\phi}\\)"
            },
        "dl.box-seq" :
            { "name" : "dl.box-seq",
              "label" : "\\(\\left(\\left[~;~\\right]\\right) \\frac{\\left[\\alpha\\right]\\left[\\beta\\right]\\phi}{\\left[\\alpha;\\beta\\right]\\phi}\\)"
            },
        "dl.box-test" :
            { "name" : "dl.box-test",
              "label" : "\\(\\left(\\left[?\\right]\\right) \\frac{H \\rightarrow \\phi)}{\\left[?H\\right]\\phi}\\)"
            },
        "dl.cut" :
            { "name" : "dl.cut",
              "label" : "\\(\\left(\\text{cut}\\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta \\quad \\Gamma,\\phi ~\\vdash~ \\Delta}{\\Gamma ~\\vdash~ \\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "\\(\\phi\\)", "placeholder" : "Formula", "type" : "text" } ]
            },
        "dl.diffcut" :
            { "name" : "dl.diffcut",
              "label" : "\\(\\left(\\text{diff. cut}\\right) \\frac{\\Gamma ~\\vdash~ \\left[x'=\\theta \\& H \\right] C, \\Delta \\quad \\Gamma ~\\vdash~ \\left[x'=\\theta \\& H \\wedge C \\right]\\phi, \\Delta}{\\Gamma ~\\vdash~ \\left[x' = \\theta \\& H \\right] \\phi, \\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "\\(C\\)", "placeholder" : "Formula", "type" : "text" } ]
            },
        "dl.diffsolution" :
            { "name" : "dl.diffsolution",
              "label" : "\\(\\left(\\text{ODE solve}\\right) \\frac{\\Gamma, H \\wedge S ~\\vdash~ \\Delta}{\\Gamma ~\\vdash~ \\left[x' = \\theta \\& H \\right] \\phi, \\Delta} \\text{ where } S \\text{ solves } x'=\\theta\\)",
            },
        "dl.qe" :
            { "name" : "dl.qe",
              "label" : "\\(\\left(\\text{QE}\\right) \\frac{\\text{QE}(\\phi)}{\\phi} \\)",
              "input" : [ { "name" : "0", "label" : "Tool", "placeholder" : "Mathematica", "type" : "text" } ]
            },
        "dl.diffinvariant" :
            {
                "name" : "dl.diffinvariant",
                "label" : makeRuleLabel("\\text{DI}",
                "\\Gamma, H ~\\vdash~ F, \\Delta \\quad \\Gamma ~\\vdash~\\forall^{\\alpha}(H \\rightarrow F_{x_1, \\ldots , x_n}^{\\theta_1, \\ldots , \\theta_n}, \\Delta)",
                "\\Gamma ~\\vdash~ \\left[ x_1' = \\theta_1, \\ldots , x_n' = \\theta_n, H \\right]F, \\Delta")
            },
        "dl.diffweaken" :
            {
                "name" : "dl.diffweaken",
                "label" : makeRuleLabel("\\text{DW}",
                "\\Gamma ~\\vdash~\\forall^{\\alpha}(H \\rightarrow \\phi, \\Delta)",
                "\\Gamma ~\\vdash~ \\left[ x' = \\theta \\& H \\right]\\phi, \\Delta")
            },
        "dl.diffconstify" :
            {
                "name" : "dl.diffconstify",
                "label" : makeRuleLabel("\\text{Dconstify}",
                "\\Gamma(\\theta()) ~\\vdash~ \\left[ x' = \\theta() \\& H(\\theta()) \\right]\\phi(\\theta()), \\Delta(\\theta())",
                "\\Gamma ~\\vdash~ \\left[ x' = \\theta \\& H \\right]\\phi, \\Delta")
            },
        "dl.equalityRewriting" :
            { "name" : "dl.equalityRewriting",
              "label" : "\\(\\left(= \\text{rewrite}\\right) \\frac{\\Gamma, \\phi(t) ~\\vdash \\psi(t), \\Delta}{\\Gamma, x=t, \\phi(x) ~\\vdash \\psi(x), \\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "Assumption", "placeholder" : "ante:3", "type" : "text" },
                          { "name" : "1", "label" : "Position", "placeholder" : "succ:2,0", "type" : "text" },
                          { "name" : "2", "label" : "Disjoint", "placeholder" : "true", "type" : "text" }
               ]
            },
        "dl.instantiate" :
            { "name" : "dl.instantiate",
              "label" : "\\(\\left(\\forall l\\right) \\frac{\\Gamma,\\phi(X) ~\\vdash~ \\Delta}{\\Gamma, \\forall x \\phi(x) ~\\vdash~ \\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "x", "placeholder" : "v", "type" : "text" },
                          { "name" : "1", "label" : "X", "placeholder" : "term", "type" : "text" }
               ]
            },
        "dl.axiomClose" :
            { "name" : "dl.axiomClose",
              "label" : "\\(\\left(\\text{axiom close}\\right) \\frac{*}{\\Gamma,\\phi ~\\vdash~ \\phi,\\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "antecedent", "placeholder" : "ante:0", "type" : "text" },
                          { "name" : "1", "label" : "succedent", "placeholder" : "succ:1", "type" : "text" }
               ]
            },
        "dl.hide" :
            { "name" : "dl.hide",
              "label" : "\\(\\left(\\text{weaken}\\right) \\frac{\\Gamma ~\\vdash~ \\Delta}{\\Gamma,\\phi ~\\vdash~ \\psi,\\Delta}\\)"
            },
        "keymaerax.arithmetic" :
            { "name" : "keymaerax.arithmetic",
              "label" : "\\(\\left(\\text{QE}\\right) \\frac{QE(\\forall X. \\Phi(X) ~\\vdash~ \\Psi(X))}{\\Phi(X_1,\\ldots,X_n) ~\\vdash~ \\Psi(X_1,\\ldots,X_n)}\\)"
            },
        "keymaerax.defaultNoArith" :
            { "name" : "keymaerax.defaultNoArith",
              "label" : "KeYmaera X Master Tactic without Arithmetic"
            },
        "keymaerax.propositional" :
            { "name" : "keymaerax.propositional",
              "label" : "KeYmaera X Propositional Tactic"
            },
        "keymaerax.default":
            { "name" : "keymaerax.default",
              "label" : "KeYmaera X Master Tactic"
            },
        "keymaerax.step":
            { "name": "keymaerax.step",
              "label": "KeYmaera X Step Tactic"
            }
    };
    var userTactics = {
        // TODO has to come from the database
    };

    var dispatchedTacticsIds = [];

    var dispatchedTacticsNotificationService = {};
    dispatchedTacticsNotificationService.broadcastDispatchedTactics = function(tId) {
        $rootScope.$broadcast('handleDispatchedTactics', tId);
    };
//    dispatchedTacticsNotificationService.broadcastDispatchedTerm = function(termId) {
//            $rootScope.$broadcast('handleDispatchedTerm', termId);
//        };


    return {
        getRuleTactics: function() { return ruleTactics; },
        getUserTactics: function() { return userTactics; },
        getDispatchedTactics: function() { return dispatchedTacticsIds; },
        addDispatchedTactics: function(tId) { dispatchedTacticsIds.push(tId); },
        removeDispatchedTactics: function(tId) {
            var i;
            while((i = arr.indexOf(item)) !== -1) { arr.splice(i, 1); }
        },
        getDispatchedTacticsNotificationService: function() { return dispatchedTacticsNotificationService; }
    };
});