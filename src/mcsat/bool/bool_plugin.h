/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */
 
#ifndef BOOL_PLUGIN_H_
#define BOOL_PLUGIN_H_

#include "mcsat/plugin.h"
#include "mcsat/clause.h"

/** Allocate a new bool plugin and setup the plugin-interface method */
plugin_t* bool_plugin_allocator(void);

const mcsat_clause_info_interface_t* bool_plugin_clause_info(plugin_t* bool_plugin);

#endif /* BOOL_PLUGIN_H_ */
