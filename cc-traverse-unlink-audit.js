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
 * Cycle collection audit for Traverse and Unlink method
 *
 * This script finds classes that participate in cycle collection but
 * do not touch all of their pointer container members in either
 * Traverse or Unlink.
 *
 * The output is, for each found class method, the method name (including
 * owning class) and the pointer fields not touched.
 */

"use strict";


// may not or may not work depending on where the source tree is located
include('../ccdehydra/ccbase.js')



// General functions for navigating Dehydra data
// See also http://wiki.mozilla.org/Dehydra_API

/**
 * Generate the flattened list of 'Dehydra items' for the given
 * function body.
 */
function body_items(body) {
  for each (let bodyItem in body) {
    for each (let stmtItem in bodyItem.statements) {
      for each (let item in item_items(stmtItem)) yield item;
    }
  }
}

/**
 * Generate the flattened list of 'Dehydra items' nested under the
 * given item, including the item itself.
 */
function item_items(item) {
  yield item;
  for each (let subitem in item.assign) {
    for each (let ans in item_items(subitem)) {
      yield ans;
    }
  }
  if (item.fieldOf) {
    for each (let ans in item_items(item.fieldOf)) {
      yield ans;
    }
  }
  for each (let subitem in item.arguments) {
    for each (let ans in item_items(subitem)) {
      yield ans;
    }
  }
}

/**
 * Search for a class type nested inside a dehydra type structure.
 *   type     a dehydra type
 *   name     the name of a C++ class
 *
 * If type represents the type 'name', 'pointer to name', or 'reference
 * to name', return the dehydra type representing class 'name'. Otherwise
 * return undefined.
 */

// probably want to use this again. may also need de-varianting.
function type_search_orig(type, name) {
  //debug_print ("Shoom: " + type.name);
  if (type.name == name && !type.parameters) return type;
  if ((type.isPointer || type.isReference) && type.type.name == name)
    return type.type;
  return undefined;
}

/**
 * Test whether a dehydra type can be used to access fields of the
 * given class.
 *   type     a dehydra type
 *   cls      a dehydra type representing a class
 *
 * Return true if 'type' is a subtype of 'cls' or a pointer or reference
 * to such a subtype.
 */
function type_fieldable(type, cls) {
  while (type.isPointer || type.isReference) {
    type = type.type;
  }
  return subtype(type, cls);
}


/**
 * Return true if ctype is a subtype of cls.
 */
function subtype(t1, t2) {
  if (t1 === t2) return true;
  for each (let {type:t1b} in t1.bases) {
    if (subtype(t1b, t2)) return true;
  }
}


function item_is_field_of (item, cls) {
  if (subtype(cls, item.memberOf))
    return true;
  if (item.fieldOf === undefined)
    return false;
  if (item.fieldOf.memberOf !== cls)
    return false;
  return true;
}


/*
 * Because the inherited analysis looks at header files, it can be
 * very spammy.  As a quick hack, we define classes that we know have
 * bad inherited classes, and print a debug message instead of
 * analyzing them.  I'm not going to bother with everything here, but
 * I'll add a few of the worst offenders.
 */
let known_bad_inherited =
  {
    "nsGenericHTMLFrameElement" : true,
    "nsHTMLFormElement" : true
  }


/*
 * If t is a cycle collector inner class lacking a Traverse or Unlink,
 * do an inherited analysis of the missing method.
 */
function process_type(t) {
  if (!is_cc_inner_class(t))
    return;
  let has_traverse = false;
  let has_unlink = false;

  for each (let m in t.members) {
    if (!m.isFunction)
      continue;
    if (m.shortName === "Traverse") {
      has_traverse = true;
      continue;
    }
    if (m.shortName === "Unlink") {
      has_unlink = true;
      continue
    }
  }

  if (!has_traverse || !has_unlink) {
    let cls = t.memberOf;

    if (known_bad_inherited[cls.name]) {
      debug_print("Skipping class " + cls.name + " with known bad inherited.");
      debug_print("");
      return;
    }

    if (t.bases === undefined || t.bases.length !== 1) {
      throw Error("Expected cycle collector class " + t.name +
		  " to have exactly one parent.");
    }
    let parent = t.bases[0].type.memberOf;
    if (parent === undefined) {
      // This could probably happen, if the parent of the inner cycle
      // collector class is something like
      // nsXPCOMCycleCollectionParticipant, but just give up for now.

      // If that actually happens, probably should check that the name
      // of the parent cycle collector class is one of the classes we
      // expected.  Then we need to change check_inherited_function to
      // treat an undefined parent as undefined, which should be easy.
      throw Error ("Expected cycle collector class parent to be a member " +
		   "of another class.");
    }

    if (!has_traverse)
      check_inherited_function(parent, cls, "Traverse");
    if (!has_unlink)
      check_inherited_function(parent, cls, "Unlink");
  }
}


/**
 * Regular expression for finding cycle collector inner classes.
 */
var method_rexp = /^(.+)::cycleCollection/;


function process_function(decl, body) {
  if (decl.shortName != "Traverse" &&
      decl.shortName != "Unlink")
    return;
  if (decl.memberOf.kind != "class")
    return;
  let match = method_rexp.exec(decl.memberOf.name);
  if (match === null)
    return;
  check_function(decl, body, decl.memberOf.memberOf, decl.shortName);
}


// give a shorter name if a field comes from the current class
function field_name (cname, m) {
  if (m.name.indexOf(cname + "::") === 0) {
    return m.shortName;
  } else {
    return m.name;
  }
}


function analyze_parent_call (parent, fields) {
  let found_any = false;
  for (let {field:m, certain:cert} in find_ptrs(parent)) {
    if (cert && fields[m.name] === false) {
      debug_print ("    found " + m.name + " in parent");
      fields[m.name] = true;
      found_any = true;
    }
  }
  return found_any;
}


// Build the list of fields in the desired class.
// Map XPCOM pointer fields -> referenced or not
function expected_fields(cls, trUn) {
  let fields = new Object();
  let odd_fields = new Object();
  for (let {field:m, certain:cert} in find_ptrs(cls, trUn === "Unlink")) {
    if (cert) {
      fields[m.name] = false;
      debug_print ("    ++ " + field_name(cls.name, m));
    } else {
      odd_fields[m.name] = false;
      debug_print("    -- " + type_name_string(m.type) + " " + field_name(cls.name, m));
    }
  }

  return {expected:fields, unexpected:odd_fields};
}


function check_inherited_function(parent, cls, trUn) {
  debug_print("Checking inherited " + trUn + " for class " + cls.name + ".");
  let {expected:fields} = expected_fields(cls, trUn);
  // no need to check unexpected fields here, as we're not visiting any
  debug_print("");
  let found_any = analyze_parent_call(parent, fields);
  if (found_any)
    debug_print("");

  // Now copy answers into an array and print
  let unrefed = new Array();
  for (let [name,b] in Iterator(fields)) {
    if (!b) unrefed.push(name);
  }

  if (unrefed.length) {
    unrefed.sort();
    tprint("Unrefed fields in inherited " + trUn + " for class " + cls.name + ":");
    tprint("  (" + cls.loc + ")");
    for each (let name in unrefed) {
      // should really strip down the name a bit
      tprint("    " + name);
    }
    tprint("");
  }

}


function check_function(decl, body, cls, trUn) {
  debug_print("Checking " + trUn + " for class " + cls.name + ".");
  let {expected:fields, unexpected:odd_fields} = expected_fields(cls, trUn);
  let found_any = false;
  debug_print("");

  // Now look for references to those fields.
  for (let item in body_items(body)) {

    // See if item is a call to a parent's traverse/unlink function.
    if (item.isFcall &&
	item.shortName === trUn &&
	item.memberOf !== undefined &&
	item.memberOf.memberOf !== undefined) {
      found_any |= analyze_parent_call(item.memberOf.memberOf, fields);
    }
    
    if (!item_is_field_of(item, cls))
      continue;
    if (fields[item.name] === false) {
      debug_print ("    found " + field_name(cls.name, item));
      found_any = true;
      fields[item.name] = true;
    } else if (odd_fields[item.name] === false) {
      debug_print ("    found unexpected field " + field_name(cls.name, item));
      found_any = true;
      odd_fields[item.name] = true;
    }

  }

  if (found_any)
    debug_print("");

  // Now copy answers into an array and print
  let unrefed = new Array();
  for (let [name,b] in Iterator(fields)) {
    if (!b) unrefed.push(name);
  }

  if (unrefed.length) {
    unrefed.sort();
    tprint("Unrefed fields in " + decl.name + ":");
    tprint("  (" + decl.loc + ")");
    for each (let name in unrefed) {
      // should really strip down the name a bit
      tprint("    " + name);
    }
    tprint("");
  }

}