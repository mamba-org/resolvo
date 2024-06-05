#define CATCH_CONFIG_MAIN
#include <resolvo.h>
#include <resolvo_pool.h>

#include <sstream>

#include "catch2/catch.hpp"

/**
 * A single candidate for a package.
 */
struct Candidate {
    resolvo::NameId name;
    uint32_t version;
    resolvo::Dependencies dependencies;
};

/**
 * A requirement for a package.
 */
struct Requirement {
    resolvo::NameId name;
    uint32_t version_start;
    uint32_t version_end;
};

/**
 * A simple database of packages that also implements resolvos DependencyProvider interface.
 */
struct PackageDatabase : public resolvo::DependencyProvider {
    resolvo::Pool<resolvo::NameId, resolvo::String> names;
    resolvo::Pool<resolvo::StringId, resolvo::String> strings;
    std::vector<Candidate> candidates;
    std::vector<Requirement> requirements;

    /**
     * Allocates a new requirement and return the id of the requirement.
     */
    resolvo::VersionSetId alloc_requirement(std::string_view package, uint32_t version_start,
                                            uint32_t version_end) {
        auto name_id = names.alloc(std::move(package));
        auto id = resolvo::VersionSetId{static_cast<uint32_t>(requirements.size())};
        requirements.push_back(Requirement{name_id, version_start, version_end});
        return id;
    }

    /**
     * Allocates a new candidate and return the id of the candidate.
     */
    resolvo::SolvableId alloc_candidate(std::string_view name, uint32_t version,
                                        resolvo::Dependencies dependencies) {
        auto name_id = names.alloc(std::move(name));
        auto id = resolvo::SolvableId{static_cast<uint32_t>(candidates.size())};
        candidates.push_back(Candidate{name_id, version, dependencies});
        return id;
    }

    resolvo::String display_name(resolvo::NameId name) override {
        return resolvo::String(names[name]);
    }

    resolvo::String display_solvable(resolvo::SolvableId solvable) override {
        const auto& candidate = candidates[solvable.id];
        std::stringstream ss;
        ss << names[candidate.name] << "=" << candidate.version;
        return resolvo::String(ss.str());
    }

    resolvo::String display_merged_solvables(
        resolvo::Slice<resolvo::SolvableId> solvables) override {
        if (solvables.empty()) {
            return resolvo::String();
        }

        std::stringstream ss;
        ss << names[candidates[solvables[0].id].name];

        bool first = true;
        for (const auto& solvable : solvables) {
            if (!first) {
                ss << " | ";
                first = false;
            }

            ss << candidates[solvable.id].version;
        }

        return resolvo::String(ss.str());
    }

    resolvo::String display_version_set(resolvo::VersionSetId version_set) override {
        const auto& req = requirements[version_set.id];
        std::stringstream ss;
        ss << req.version_start << ".." << req.version_end;
        return resolvo::String(ss.str());
    }

    resolvo::String display_string(resolvo::StringId string_id) override {
        return strings[string_id];
    }

    resolvo::NameId version_set_name(resolvo::VersionSetId version_set_id) override {
        return requirements[version_set_id.id].name;
    }

    resolvo::NameId solvable_name(resolvo::SolvableId solvable_id) override {
        return candidates[solvable_id.id].name;
    }

    resolvo::Candidates get_candidates(resolvo::NameId package) override {
        resolvo::Candidates result;

        for (uint32_t i = 0; i < static_cast<uint32_t>(candidates.size()); ++i) {
            const auto& candidate = candidates[i];
            if (candidate.name != package) {
                continue;
            }
            result.candidates.push_back(resolvo::SolvableId{i});
            result.hint_dependencies_available.push_back(resolvo::SolvableId{i});
        }

        result.favored = nullptr;
        result.locked = nullptr;

        return result;
    }

    void sort_candidates(resolvo::Slice<resolvo::SolvableId> solvables) override {
        std::sort(solvables.begin(), solvables.end(),
                  [&](resolvo::SolvableId a, resolvo::SolvableId b) {
                      return candidates[a.id].version > candidates[b.id].version;
                  });
    }

    resolvo::Vector<resolvo::SolvableId> filter_candidates(
        resolvo::Slice<resolvo::SolvableId> solvables, resolvo::VersionSetId version_set_id,
        bool inverse) override {
        resolvo::Vector<resolvo::SolvableId> result;
        const auto& requirement = requirements[version_set_id.id];
        for (auto solvable : solvables) {
            const auto& candidate = candidates[solvable.id];
            bool matches = candidate.version >= requirement.version_start &&
                           candidate.version < requirement.version_end;
            if (matches != inverse) {
                result.push_back(solvable);
            }
        }
        return result;
    }

    resolvo::Dependencies get_dependencies(resolvo::SolvableId solvable) override {
        const auto& candidate = candidates[solvable.id];
        return candidate.dependencies;
    }
};

#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#elif defined(__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-variable"
#endif

SCENARIO("Solve") {
    /// Construct a database with packages a, b, and c.
    PackageDatabase db;

    auto a_1 = db.alloc_candidate("a", 1, {{db.alloc_requirement("b", 1, 4)}, {}});
    auto a_2 = db.alloc_candidate("a", 2, {{db.alloc_requirement("b", 1, 4)}, {}});
    auto a_3 = db.alloc_candidate("a", 3, {{db.alloc_requirement("b", 4, 7)}, {}});

    auto b_1 = db.alloc_candidate("b", 1, {});
    auto b_2 = db.alloc_candidate("b", 2, {});
    auto b_3 = db.alloc_candidate("b", 3, {});

    auto c_1 = db.alloc_candidate("c", 1, {});

    // Construct a problem to be solved by the solver
    resolvo::Vector<resolvo::VersionSetId> requirements = {db.alloc_requirement("a", 1, 3)};
    resolvo::Vector<resolvo::VersionSetId> constraints = {db.alloc_requirement("b", 1, 3),
                                                          db.alloc_requirement("c", 1, 3)};

    // Solve the problem
    resolvo::Vector<resolvo::SolvableId> result;
    resolvo::solve(db, requirements, constraints, result);

    // Check the result
    REQUIRE(result.size() == 2);
    REQUIRE(result[0] == a_2);
    REQUIRE(result[1] == b_2);
}
