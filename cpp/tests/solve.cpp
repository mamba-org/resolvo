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
 * A version set for a package.
 */
struct VersionSet {
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
    std::vector<resolvo::Condition> conditions;
    std::vector<Candidate> candidates;
    std::vector<VersionSet> version_sets;
    std::vector<std::vector<resolvo::VersionSetId>> version_set_unions;

    /**
     * Allocates a new version set and return the id of the version set.
     */
    resolvo::VersionSetId alloc_version_set(std::string_view package, uint32_t version_start,
                                            uint32_t version_end) {
        auto name_id = names.alloc(std::move(package));
        auto id = resolvo::VersionSetId{static_cast<uint32_t>(version_sets.size())};
        version_sets.push_back(VersionSet{name_id, version_start, version_end});
        return id;
    }

    /**
     * Allocates a new requirement for a single version set.
     */
    resolvo::Requirement alloc_requirement(std::string_view package, uint32_t version_start,
                                           uint32_t version_end) {
        auto id = alloc_version_set(package, version_start, version_end);
        return {id};
    }

    /**
     * Allocates a new requirement for a version set union.
     */
    resolvo::Requirement alloc_requirement_union(
        std::initializer_list<std::tuple<std::string_view, uint32_t, uint32_t>> version_sets) {
        std::vector<resolvo::VersionSetId> version_set_union{version_sets.size()};

        auto version_sets_it = version_sets.begin();
        for (size_t i = 0; i < version_sets.size(); ++i, ++version_sets_it) {
            auto [package, version_start, version_end] = *version_sets_it;
            version_set_union[i] = alloc_version_set(package, version_start, version_end);
        }

        resolvo::VersionSetUnionId id = {static_cast<uint32_t>(version_set_unions.size())};
        version_set_unions.push_back(std::move(version_set_union));
        return {id};
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

    /**
     * Allocates a new candidate and return the id of the candidate.
     */
    resolvo::ConditionId alloc_condition(resolvo::Condition condition) {
        auto id = resolvo::ConditionId{static_cast<uint32_t>(conditions.size())};
        conditions.push_back(condition);
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
        ss << names[candidates[solvables[0].id].name] << " ";

        bool first = true;
        for (const auto& solvable : solvables) {
            if (!first) {
                ss << " | ";
            } else {
                first = false;
            }

            ss << candidates[solvable.id].version;
        }

        return resolvo::String(ss.str());
    }

    resolvo::String display_version_set(resolvo::VersionSetId version_set) override {
        const auto& req = version_sets[version_set.id];
        std::stringstream ss;
        ss << req.version_start << ".." << req.version_end;
        return resolvo::String(ss.str());
    }

    resolvo::String display_string(resolvo::StringId string_id) override {
        return strings[string_id];
    }

    resolvo::NameId version_set_name(resolvo::VersionSetId version_set_id) override {
        return version_sets[version_set_id.id].name;
    }

    resolvo::NameId solvable_name(resolvo::SolvableId solvable_id) override {
        return candidates[solvable_id.id].name;
    }

    resolvo::Slice<resolvo::VersionSetId> version_sets_in_union(
        resolvo::VersionSetUnionId version_set_union_id) override {
        const auto& version_set_ids = version_set_unions[version_set_union_id.id];
        return {version_set_ids.data(), version_set_ids.size()};
    }

    resolvo::Condition resolve_condition(resolvo::ConditionId condition_id) override {
        return conditions[condition_id.id];
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
        const auto& version_set = version_sets[version_set_id.id];
        for (auto solvable : solvables) {
            const auto& candidate = candidates[solvable.id];
            bool matches = candidate.version >= version_set.version_start &&
                           candidate.version < version_set.version_end;
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

    // Check that PackageDatabase correctly implements the DependencyProvider interface
    static_assert(std::has_virtual_destructor_v<PackageDatabase>);
    static_assert(std::is_polymorphic_v<PackageDatabase>);
    static_assert(std::is_base_of_v<resolvo::DependencyProvider, PackageDatabase>);

    auto a_1 = db.alloc_candidate("a", 1, {{db.alloc_requirement("b", 1, 4)}, {}});
    auto a_2 = db.alloc_candidate("a", 2, {{db.alloc_requirement("b", 1, 4)}, {}});
    auto a_3 = db.alloc_candidate("a", 3, {{db.alloc_requirement("b", 4, 7)}, {}});

    auto b_1 = db.alloc_candidate("b", 1, {});
    auto b_2 = db.alloc_candidate("b", 2, {});
    auto b_3 = db.alloc_candidate("b", 3, {});

    auto c_1 = db.alloc_candidate("c", 1, {});

    const auto d_1 = db.alloc_candidate("d", 1, {});

    // Construct a problem to be solved by the solver
    resolvo::Vector<resolvo::ConditionalRequirement> requirements = {
        db.alloc_requirement("a", 1, 3)};
    resolvo::Vector<resolvo::VersionSetId> constraints = {
        db.alloc_version_set("b", 1, 3),
        db.alloc_version_set("c", 1, 3),
        db.alloc_version_set("d", 2, 2),
    };
    resolvo::Vector soft_requirements{c_1, d_1};

    // Solve the problem
    resolvo::Vector<resolvo::SolvableId> result;
    resolvo::Problem problem = {requirements, constraints, soft_requirements};
    resolvo::solve(db, problem, result);

    // Check the result
    REQUIRE(result.size() == 3);
    REQUIRE(result[0] == a_2);
    REQUIRE(result[1] == b_2);
    REQUIRE(result[2] == c_1);
}

SCENARIO("Solve conditional") {
    /// Construct a database with packages a, b, and c.
    PackageDatabase db;

    auto b_cond_version_set = db.alloc_version_set("b", 1, 3);
    auto b_cond = db.alloc_condition({b_cond_version_set});
    auto a_cond_req = resolvo::ConditionalRequirement{&b_cond, db.alloc_requirement("a", 1, 3)};

    auto a_1 = db.alloc_candidate("a", 1, {{}, {}});
    auto b_1 = db.alloc_candidate("b", 1, {{}, {}});
    auto c_1 = db.alloc_candidate("c", 1, {{a_cond_req}, {}});

    // Construct a problem to be solved by the solver
    resolvo::Vector<resolvo::ConditionalRequirement> requirements = {
        db.alloc_requirement("b", 1, 3), db.alloc_requirement("c", 1, 3)};

    // Solve the problem
    resolvo::Vector<resolvo::SolvableId> result;
    resolvo::Problem problem = {requirements, {}, {}};
    resolvo::solve(db, problem, result);

    // Check the result
    REQUIRE(result.size() == 3);
    REQUIRE(result[0] == c_1);
    REQUIRE(result[1] == b_1);
    REQUIRE(result[2] == a_1);
}

SCENARIO("Solve Union") {
    /// Construct a database with packages a, b, and c.
    PackageDatabase db;

    // Check that PackageDatabase correctly implements the DependencyProvider interface
    static_assert(std::has_virtual_destructor_v<PackageDatabase>);
    static_assert(std::is_polymorphic_v<PackageDatabase>);
    static_assert(std::is_base_of_v<resolvo::DependencyProvider, PackageDatabase>);

    auto a_1 = db.alloc_candidate("a", 1, {});

    auto b_1 = db.alloc_candidate("b", 1, {});

    auto c_1 = db.alloc_candidate("c", 1, {{db.alloc_requirement("a", 1, 10)}, {}});

    auto d_1 = db.alloc_candidate("d", 1, {{db.alloc_requirement("b", 1, 10)}, {}});

    auto e_1 = db.alloc_candidate("e", 1,
                                  {{db.alloc_requirement_union({{"a", 1, 10}, {"b", 1, 10}})}, {}});

    auto f_1 = db.alloc_candidate(
        "f", 1, {{db.alloc_requirement("b", 1, 10)}, {db.alloc_version_set("a", 10, 20)}});

    // Construct a problem to be solved by the solver
    resolvo::Vector<resolvo::ConditionalRequirement> requirements = {
        db.alloc_requirement_union({{"c", 1, 10}, {"d", 1, 10}}),
        db.alloc_requirement("e", 1, 10),
        db.alloc_requirement("f", 1, 10),
    };
    resolvo::Vector<resolvo::VersionSetId> constraints = {};

    // Solve the problem
    resolvo::Vector<resolvo::SolvableId> result;
    resolvo::Problem problem = {requirements, constraints, {}};
    auto error = resolvo::solve(db, problem, result);

    // Check the result
    REQUIRE(result.size() == 4);
    REQUIRE(result[0] == f_1);
    REQUIRE(result[1] == e_1);
    REQUIRE(result[2] == b_1);
    REQUIRE(result[3] == d_1);
}
