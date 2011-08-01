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
  if (match == null)
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


function check_function(decl, body, cls, trUn) {
  debug_print("Checking " + trUn + " for class " + cls.name + ".");
  // Build the list of fields in the desired class.
  // Map XPCOM pointer fields -> referenced or not
  let fields = new Object();

  for (let m in find_ptrs(cls, trUn === "Unlink")) {
    fields[m.name] = false
    debug_print ("    ++ " + field_name(cls.name, m));
  }

  let found_any = false;
  debug_print("");

  // Now look for references to those fields.
  for (let item in body_items(body)) {

    // See if item is a call to a parent's traverse/unlink function.
    if (item.isFcall &&
	item.shortName === trUn &&
	item.memberOf !== undefined &&
	item.memberOf.memberOf !== undefined) {
      for (let m in find_ptrs(item.memberOf.memberOf)) {
	if (fields[m.name] === false) {
	  debug_print ("    found " + m.name + " in parent");
	  fields[m.name] = true;
	  found_any = true;
	}
      }
    }
    
      /*
    if (cls.name === "NotificationController" &&
	item.shortName === "mHangingChildDocuments") {
      //print ("flint: " + (item.memberOf === cls));
      do_dehydra_dump(item, 0, 4);
      print ("");
    }*/

    /*
    if (item.name === "nsINode::mNodeInfo") {
      do_dehydra_dump(item, 0, 4);
      print ("");
    }
    */

    if (!item_is_field_of(item, cls))
      continue;
    if (fields[item.name] === false) {
      debug_print ("    found " + field_name(cls.name, item));
      found_any = true;
      fields[item.name] = true;
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
      tprint("    " + name);
    }
    tprint("");
  }

}