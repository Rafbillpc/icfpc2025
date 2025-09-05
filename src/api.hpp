#pragma once

#include "layout.hpp"

string get_problem_name(int size);
void api_select(string const& problem);
vector<vector<int>> api_explore(vector<string> const& data);
bool api_guess(layout const& L);
