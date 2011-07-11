/* ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1/GPL 2.0/LGPL 2.1
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * The Original Code is mozilla.org code.
 *
 * The Initial Developer of the Original Code is
 * The Mozilla Foundation.
 * Portions created by the Initial Developer are Copyright (C) 2011
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Andrew McCreight, Mozilla Corporation
 *   David Mandelin, Mozilla Corporation
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU General Public License Version 2 or later (the "GPL"), or
 * the GNU Lesser General Public License Version 2.1 or later (the "LGPL"),
 * in which case the provisions of the GPL or the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of either the GPL or the LGPL, and not to allow others to
 * use your version of this file under the terms of the MPL, indicate your
 * decision by deleting the provisions above and replace them with the notice
 * and other provisions required by the GPL or the LGPL. If you do not delete
 * the provisions above, a recipient may use your version of this file under
 * the terms of any one of the MPL, the GPL or the LGPL.
 *
 * ***** END LICENSE BLOCK ***** */


/** 
 * Dehydra script
 * Cycle collection audit for classes that should use CC but don't.
 *
 * This script finds classes that (a) are concrete, (b) implement
 * nsISupports, (c) do not participate in cycle collection, and
 * (d) have XPCOM pointer container member fields. Such classes are
 * suspected of needing to be converted to use CC.
 *
 * The output is, for each 'bad' class, the class name, followed by
 * the pointer container members.
 */

// Incorporates class hierarchy analysis from type-printer.js

"use strict";


// may not or may not work depending on where the source tree is located
include('../ccdehydra/ccbase.js')



/*
 * This structure contains fields that should be ignored for the
 * type-based cycle analysis.
 */
let whitelist = {
  "nsCSSStyleSheet::mNext" : true,  // bz says CSS style sheets only form trees
  "nsIDocument::mSecurityInfo" : true // some kind of deserialized thing, maybe not okay?
}


/*
 * Classes that can be exposed as JS objects.  These can contain
 * arbitrary other objects that can be exposed as JS objects.
 */
let jsExposedNames = {
  //"moz::dom::Element" : true ???
  //"nsIObserver" : true,
  "nsINode" : true,
  "nsIRange" : true,
  "nsIDocument" : true,
  "nsINodeList" : true,
  "nsIContent" : true   // ??
// nsIDomWindow ?
}


// store the definitions of the types that are exposed and were encountered
let jsExposedTypes = []

// store all the types we encountered
let typelist = [];

/**
 * Function for generating error output. The version with the prefix
 * is used to allow output to be easily collected from a mixed file.
 */
function tprint(s) {
  //print("$D$ " + s);
  print("CCA::" + s);
}


// uncomment out this line to print out a reason why a class is not cycle collected
function print_reason_ok(type, rsn) {
  //tprint ("type " + type.name + " is okay because it " + rsn);
}




// Store a list of all subtypes of nsISupports.  Should rename this to
// is_nsISupports or something, and not save results at every
// intermediate step, though I want to be sure that doesn't result in
// less being added.
function interesting_type(t)
{
  let name = t.name;
  if (name === undefined)
    return false;
  if (t.typedef !== undefined)
    return interesting_type(t.typedef);

  if (name === 'nsISupports') {
    if (!typelist.some(function (u) u === t))
      typelist.push(t);
    return true;
  }

  for each (let {type:base} in t.bases) {
    if (base.name === undefined) {
      throw Error("Nameless type on a subcall.");
    }
    if (interesting_type(base)) {
      if (!typelist.some(function (u) u === t))
	typelist.push(t);
      if (jsExposedNames[t.name] &&
	  !jsExposedTypes.some(function (u) u.name === t.name)) {
	jsExposedTypes.push(t);
      }
      return true;
    }
  }
  
  return false;
}


// store immediate subtypes of classes
function add_subtype(t, subt)
{
  if (subt.typedef === undefined &&
      subt.kind === undefined)
    throw Error("Unexpected subtype: not class or typedef: " + subt);

  if (t.subtypes === undefined)
    t.subtypes = [];

  if (!t.subtypes.some(function (u) u === subt)) {
    //if (t.name !== 'nsISupports')
    //  print(subt.name + " <: " + t.name);
    t.subtypes.push(subt);
  }

}


function process_type(t)
{
  if (t.typedef !== undefined || t.name === undefined)
    return;
  if (is_cc_inner_class(t)) {
    if (t.memberOf === undefined)
      throw Error("Expected cycle collector helper class to be the member of another class.");
    cctypes.push(t.memberOf);
    return;
  }
  if (nsiContentCache === undefined && t.name === 'nsIContent') {
    nsiContentCache = t;
  }
  if (interesting_type(t)) {
    for each (let {type:base} in t.bases)
      add_subtype(base, t);
  }
}


// If t is exposed to JS, add all other classes exposed to JS.
function add_js_exposed(t, tt) {
  if (jsExposedNames[t.name]) {
    for each (let u in jsExposedTypes) {
      if (!tt.some(function (v) v === u)) {
	tt.push(u);
      }
    }
  }
}


function iter_rc_edge_members(t, f) {
  for each (let m in t.members) {
    if (!m.isFunction && !whitelist[m.name]) {
      let ctype = ptr_type_contains(m.type);
      if (ctype !== undefined) {
	f(m, ctype);
      }
    }
  }
}


function add_member_type (ans) {
  return function (m, ctype) {
    if (!ans.some(function (u) u === ctype))
      ans.push(ctype);
  }
}


/**
 * Helper for find_ptrs.
 */
function do_find_ptrs(type, ans) {
  iter_rc_edge_members(type, add_member_type(ans));
  add_js_exposed(type, ans);
  for each (let {type:b} in type.bases) {
    do_find_ptrs(b, ans);
  }
}

/**
 * Return an array of dehydra member objects for all the member fields
 * of a dehydra type that are cycle-collection-related pointer types.
 * See also is_ptr_type.
 */
function find_ptrs(type) {
  let ans = new Array();
  do_find_ptrs(type, ans);
  return ans;
}


// add the transitive closure of the subclasses of all the types in the array
function add_subclasses(tt) {
  // extend the array as we traverse it
  for (let i = 0; i < tt.length; i += 1) {
    for each (let t in tt[i].subtypes) {
      if (!tt.some(function (u) u === t)) {
	//print("Adding subtype " + t.name);
	tt.push(t);
      }
    }
  }
}


// return an array containing all of the classes that t can have a
// refcounted reference to
function next_classes(t) {
  let bases = find_ptrs(t);
  add_subclasses(bases);
  return bases;
}


function type_array_string(a) {
  let s = "";
  for (let [i, {name:n}] in Iterator(a)) {
    if (i == 0)
      s = n;
    else
      s = s + ", " + n;
  }
  return s;
}


function type_string (t) {
  if (t.name !== undefined) {
    return t.name;
  }
  if (t.isPointer) {
    return type_string(t.type) + "*";
  }
  if (t.isArray) {
    return type_string(t.type) + "[]";
  }
  return "UNDEFINED";
}


function print_members (t) {
  for each (let m in t.members) {
    if (m.isFunction) {
      //print ("name:" + m.name);
    } else {
      let t2 = ptr_type_contains(m.type);
      if (t2 !== undefined) {
	print ("     " + m.name + " : " + type_string(m.type) + " --> " + type_string(t2));
      } else {
	print ("     " + m.name + " : " + type_string(m.type));
      }
    }
  }
  for each (let {type:b} in t.bases) {
    print_members(b);
  }
}


// add any edges to the same SCC
function add_scc_edges(ans, scc) {
  return function (m, t) {
    if (t.scc === scc) {
      if (!ans.some(function (u) u === t)) {
	ans.push(t);
      }
    }
  }
}


function any_lazy_parents (t) {
  if (t.name === undefined)
    throw Error ("Parent without a name.");

  if (t.name === "nsISupports")
    return false;

}

function class_scc_edges(t) {
  let scc_edges = new Array();
  iter_rc_edge_members(t, add_scc_edges(scc_edges, t.scc));
  return scc_edges;
}


function any_scc_edges(t) {
  return class_scc_edges(t).length !== 0;
}


// should probably memoize class_scc_edges, is_abstract, escaping_cc_edges, etc.

function escaping_cc_edges(t) {
  if (t.name === "nsISupports")
    return false;
  // If a class is concrete, it is responsible for capturing all CC
  // edges from parents.
  if (!is_abstract(t))
    return false;
  if (any_scc_edges(t))
    return true;
  for each (let {type:b} in t.bases) {
    if (escaping_cc_edges(b))
      return true;
  }
  return false;
}

function should_be_cced (t) {
  if (t.name === "nsISupports")
    return false;
  if (is_abstract(t))
    return false;
  if (any_scc_edges(t))
    return true;
  for each (let {type:b} in t.bases) {
    if (escaping_cc_edges(b))
      return true;
  }
  return false;
}


function analyze_cc_result(t) {
  let nc = type_array_string(find_ptrs(t));

  function print_sub_next () {
    let nc2 = type_array_string(next_classes(t));
    if (nc !== nc2) {
      tprint("   >>++ " + nc2);
    }
  }

  //if (t.name === "nsPresContext") {
    //print_members(t);
  //}

  let t_is_cc = is_cc(t);
  if (should_be_cced(t)) {
    if (t_is_cc) {
      tprint("OK::YES:: " + t.name + ">> " + nc);
    } else {
      tprint("BAD::NEED:: " + t.name + ">> " + nc);
      tprint("  SCC edges: " + type_array_string(class_scc_edges(t)));
    }
    print_sub_next();
  } else {
    if (t_is_cc) {
      tprint("BAD::UNNEEDED:: " + t.name + ">> " + nc);
      tprint("  SCC edges: " + type_array_string(class_scc_edges(t)));
      print_sub_next();
    } else {
      //if (true) {
      if (nc !== "") {
	tprint("OK::NO: " + t.name + ">> " + nc);
	print_sub_next();
      }
    }
  }

}


/*
 * Cheriyan-Mehlhorn-Gabow algorithm for finding SCCs.
 */
function find_cyclic_classes() {
  let glob = new Object();
  glob.dfs = 0;
  glob.scc = 0;
  let roots = new Array();
  let open = new Array();

  function fcc_dfs(t) {
    t.dfs = glob.dfs;
    glob.dfs += 1;
    roots.push(t);
    open.push(t);
    let edges = next_classes(t);
    for each (let u in edges) {
      if (u.dfs === undefined) {
	fcc_dfs(u);
      } else {
	if (u.scc === undefined) {
	  while (u.dfs < roots[roots.length - 1].dfs) {
	    roots.pop();
	  }
	}
      }
    }
    if (t === roots[roots.length - 1]) {
      roots.pop();
      while (true) {
	let u = open.pop();
	u.scc = glob.scc;
	if (u === t)
	  break;
      }
      glob.scc += 1;
    }
  }

  for each (let t in typelist) {
    if (t.dfs === undefined) {
      fcc_dfs(t);
    }
  }

}


function print_auto_members (t) {
  for each (let m in t.members) {
    if (!m.isFunction && m.type.template !== undefined) {
      if (m.type.template.name === 'nsAutoPtr') {
	print("has type nsAutoPtr: " + m.name + " : " + type_string(m.type));
      }
    }
  }
  //for each (let {type:b} in t.bases) {
  //  print_auto_members(b);
  //}
}


function input_end()
{
  find_cyclic_classes();
  for each (let t in typelist) {
    analyze_cc_result(t);
  }
}