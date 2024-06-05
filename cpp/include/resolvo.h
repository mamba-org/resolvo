#pragma once

#include "resolvo_dependency_provider.h"
#include "resolvo_internal.h"

namespace resolvo {

/**
 * Called to solve a package problem.
 *
 * If the solve was successful, an empty string is returned and selected solvable ids will be
 * stored in `result`. If the solve was unsuccesfull an error describing the reason is returned and
 * the result vector will be empty.
 */
String solve(DependencyProvider &provider, Slice<VersionSetId> requirements,
             Slice<VersionSetId> constraints, Vector<SolvableId> &result) {
    cbindgen_private::DependencyProvider bridge{
        static_cast<void *>(&provider),
        private_api::bridge_display_solvable,
        private_api::bridge_display_solvable_name,
        private_api::bridge_display_merged_solvables,
        private_api::bridge_display_name,
        private_api::bridge_display_version_set,
        private_api::bridge_display_string,
        private_api::bridge_version_set_name,
        private_api::bridge_solvable_name,
        private_api::bridge_get_candidates,
        private_api::bridge_sort_candidates,
        private_api::bridge_filter_candidates,
        private_api::bridge_get_dependencies,
    };

    String error;
    cbindgen_private::resolvo_solve(&bridge, requirements, constraints, &error, &result);
    return error;
}
}  // namespace resolvo
