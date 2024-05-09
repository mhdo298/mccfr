//#include <string>
#include <cstdio>
#include <algorithm>

#include <random>
#include <sstream>
#include <pthread.h>

#define THREADS 100
#define STATES 11531
#define STRATEGY_SIZE 1210442

#define index2(i1, i2) (i1 + i2  * (i2-1) / 2 )
#define index3(i1, i2, i3) (i1 + i2  * (i2-1) / 2 + i3 * (i3-1) * (i3-2) / 6)
#define index4(i1, i2, i3, i4) (i1 + i2  * (i2-1) / 2 + i3 * (i3-1) * (i3-2) / 6 + i4 * (i4-1) * (i4-2)* (i4-3) / 24 )
#define index5(i1, i2, i3, i4, i5) (i1 + i2  * (i2-1) / 2 + i3 * (i3-1) * (i3-2) / 6 + i4 * (i4-1) * (i4-2)* (i4-3) / 24+ i5 * (i5-1) * (i5-2)* (i5-3)* (i5- 4) / 120 )
#define dec3(i6, i5, i3, i2, i1) i6 = i5; if(i6 > i3) i6--;if(i6 > i2) i6--;if(i6 > i1) i6--;
#define dec4(i6, i5, i4, i3, i2, i1) i6 = i5;  if(i6 > i4) i6--;if(i6 > i3) i6--;if(i6 > i2) i6--;if(i6 > i1) i6--;
#define dec5(i6, i7, i5, i4, i3, i2, i1) i6 = i7;  if(i6 > i5) i6--; if(i6 > i4) i6--;if(i6 > i3) i6--;if(i6 > i2) i6--;if(i6 > i1) i6--;


volatile double *next_regret[THREADS];
volatile double *next_strategy[THREADS];
int *HR;
double *total_regret;
double *total_strategy;

uint32_t strategy_offset[STATES]; // indexed by state
uint16_t child[STATES * 3]; // index by state * 3 + action
uint8_t contributions[STATES * 2];
uint8_t player_at_state[STATES];

uint8_t flop_table[12994800];
uint8_t turn_table[152688900];
uint8_t river_table[1404737880];

const uint8_t preflop_table[] = {2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 4, 2, 2, 4, 4, 4, 4, 2, 2, 2, 4,
                                 4, 4,
                                 4, 4, 4,
                                 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 4, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4,
                                 2, 2,
                                 2, 4, 4,
                                 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4,
                                 4, 4,
                                 4, 4, 4,
                                 4, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
                                 4, 3,
                                 3, 3, 3,
                                 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
                                 3, 3,
                                 3, 3, 6,
                                 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 6, 6, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4,
                                 4, 4,
                                 4, 3, 3,
                                 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 6, 4, 4,
                                 4, 4,
                                 4, 4, 4,
                                 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 6, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3,
                                 3, 3,
                                 3, 3, 3,
                                 3, 6, 6, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                                 1, 1,
                                 1, 1, 1,
                                 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                                 1, 1,
                                 1, 1, 1,
                                 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                                 1, 1,
                                 1, 1, 1,
                                 1, 6, 6, 6, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
                                 8, 8,
                                 8, 8, 8,
                                 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 6, 8, 8,
                                 8, 8,
                                 8, 8, 8,
                                 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 6, 6, 8, 8, 8, 8, 8, 8,
                                 8, 8,
                                 8, 8, 8,
                                 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                                 7, 7,
                                 7, 7, 7,
                                 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                                 7, 7,
                                 7, 7, 7,
                                 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                                 7, 7,
                                 7, 7, 7,
                                 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                                 7, 7,
                                 7, 7, 7,
                                 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                                 7, 0,
                                 0, 0, 0,
                                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                                 7, 7,
                                 7, 0, 0,
                                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 7, 7, 7, 7, 7, 7,
                                 7, 7,
                                 7, 7, 7,
                                 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 7, 7,
                                 7, 7,
                                 7, 7, 7,
                                 7, 7, 7, 7, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                                 6, 6,
                                 6, 0, 0,
                                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                                 0, 0,
                                 0, 0, 0,
                                 5, 5, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                                 0, 0,
                                 0, 0, 0,
                                 0, 0, 0, 0, 0, 0, 5, 5, 5, 5, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                                 0, 0,
                                 0, 0, 0,
                                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 5, 5, 9, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                                 0, 0,
                                 0, 0, 0,
                                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 5, 5, 9, 9, 9, 5,
                                 5, 5,
                                 5, 5, 5,
                                 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
                                 5, 5,
                                 5, 5, 5,
                                 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
                                 5, 5,
                                 5, 5, 5,
                                 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
                                 5, 5,
                                 5, 5, 5,
                                 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 9, 5, 5,
                                 5, 5,
                                 5, 5, 5,
                                 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
                                 5, 5,
                                 5, 5, 5,
                                 5, 5, 5, 9, 9, 9, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                 2, 2,
                                 2, 2, 2,
                                 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                 2, 2,
                                 2, 2, 2,
                                 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                 2, 2,
                                 2, 2, 2,
                                 9, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                 2, 2,
                                 2, 2, 2,
                                 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 9, 9, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                 2, 2,
                                 2, 2, 2,
                                 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                 2, 2,
                                 9, 9, 9};
//const char RANKS[] = "23456789TJQKA";
//const char SUITS[] = "DCHS";

double utility(uint16_t state, const uint64_t eval_table[3], uint8_t player) {
    int p1 = contributions[state * 2];
    int p2 = contributions[state * 2 + 1];
    switch (player_at_state[state]) {
        case 0:
            if (p1 != p2) printf("error with nature_river");
            return eval_table[player] > eval_table[3 - player] ? p1 : -p2;
        case 3:
            return player == 1 ? -p1 : p1;
        case 4:
            return player == 2 ? -p2 : p2;
        default:
            printf("bro wtf are you doing?");
            return -1;
    }
}

double cfr(uint16_t state, const uint64_t info_sets[3], const uint64_t precalculated_vals[5][3], double prob[3],
           uint8_t player, int thread_id);

double nature_move(uint16_t state, const uint64_t precalculated_vals[5][3], double prob[3],
                   uint8_t player, uint8_t turn, int thread_id) {
    double vI = 0;
    uint16_t next = child[state * 3];
    if (turn == 8) {
        double p[3] = {prob[0] / 44, prob[1], prob[2]};
        return 1.0 / 44 * cfr(next, precalculated_vals[3], precalculated_vals, p, player, thread_id);
    }
        // flop -> turn
    else if (turn == 7) {
        double p[3] = {prob[0] / 45, prob[1], prob[2]};
        return 1.0 / 45 * cfr(next, precalculated_vals[2], precalculated_vals, p, player, thread_id);
    }
        // preflop -> flop
    else if (turn == 6) {
        double p[3] = {prob[0] / 16215, prob[1], prob[2]};
        return 1.0 / 16215 * cfr(next, precalculated_vals[1], precalculated_vals, p, player, thread_id);
    }
        // start -> preflop
    else if (turn == 5) {
        double p[3] = {1.0 / 1624350, 1, 1};
        return p[0] * cfr(next, precalculated_vals[0], precalculated_vals, p, player, thread_id);
    } else {
        printf("ok check your code plz\n");
    }
    return vI;

}

double cfr(uint16_t state, const uint64_t info_sets[3], const uint64_t precalculated_vals[5][3], double prob[3],
           uint8_t player, int thread_id) {

    uint8_t Ph = player_at_state[state];
    switch (Ph) {
        case 0:
        case 3:
        case 4:
            return utility(state, precalculated_vals[4], player);
        case 5:
        case 6:
        case 7:
        case 8:
            return nature_move(state, precalculated_vals, prob, player, Ph, thread_id);
    }
    uint32_t children[3];
    for (int i = 0; i < 3; ++i) {
        children[i] = child[state * 3 + i];
    }
    uint32_t offset = strategy_offset[state] + info_sets[Ph] * 3; // this tells us where to index into
    // 0 is fold, 1 is call, 2 is raise

    // regret matching
    double sigma[3];
    double sum = 0;
    uint8_t valid = 0;
    for (int i = 0; i < 3; ++i) {
        if (children[i]) {
            sigma[i] = total_regret[offset + i] > 0 ? total_regret[offset + i] : 0;
            valid++;
            sum += sigma[i];
        }
    }
    if (sum > 0) {
        for (int i = 0; i < 3; ++i) {
            if (children[i]) sigma[i] /= sum;
            else sigma[i] = 0;
        }
    } else {
        for (int i = 0; i < 3; ++i) {
            if (children[i]) sigma[i] = 1.0 / valid;
            else sigma[i] = 0;
        }
    }

    // recursively calling cfr and getting information
    double v[3];
    double vI = 0;
    for (int i = 0; i < 3; ++i) {
        if (!children[i]) continue; // ID 0 means not valid
        double next_prob[3] = {prob[0], prob[1], prob[2]};
        next_prob[Ph] *= sigma[i];
        v[i] = cfr(children[i], info_sets, precalculated_vals, next_prob, player, thread_id);
        vI += sigma[i] * v[i];
    }

    // update regret and strategy_1
    if (Ph == player) {
        for (int i = 0; i < 3; ++i) {
            if (children[i]) {
                next_regret[thread_id][offset + i] += prob[0] * prob[3 - player] * (v[i] - vI);
                next_strategy[thread_id][offset + i] += prob[player] * sigma[i];
            }
        }
    }
    return vI;
}

void *thread_handler(void *input) {
    int id = *(int *) (input);
    int64_t deck[52];
    std::random_device rd;
    std::mt19937 g(rd());
    for (int i = 0; i < 52; ++i) {
        deck[i] = i;
    }
    int64_t c11, c12, c21, c22, hand_1, hand_2, ind, u0;
    for (int i = 0; i < 1000; ++i) {
        std::shuffle(deck, deck + 52, g);
//        printf("deck: %llu %llu %llu %llu %llu %llu %llu %llu %llu\n", deck[0], deck[1], deck[2], deck[3], deck[4],
//               deck[5],
//               deck[6], deck[7], deck[8]);

        uint64_t precalculated_val[5][3];
        if (deck[0] > deck[1]) std::swap(deck[0], deck[1]);
        if (deck[2] > deck[3]) std::swap(deck[2], deck[3]);

        hand_1 = index2(deck[0], deck[1]);
        hand_2 = index2(deck[2], deck[3]);

        precalculated_val[0][1] = preflop_table[hand_1];
        precalculated_val[0][2] = preflop_table[hand_2];

        if (deck[4] > deck[5]) std::swap(deck[4], deck[5]);
        if (deck[5] > deck[6]) std::swap(deck[5], deck[6]);
        if (deck[4] > deck[5]) std::swap(deck[4], deck[5]);

        dec3(c11, deck[0], deck[6], deck[5], deck[4]);
        dec3(c12, deck[1], deck[6], deck[5], deck[4]);
        dec3(c21, deck[2], deck[6], deck[5], deck[4]);
        dec3(c22, deck[3], deck[6], deck[5], deck[4]);
        hand_1 = index2(c11, c12);
        hand_2 = index2(c21, c22);

        ind = index3(deck[4], deck[5], deck[6]) * 1176 + hand_1;
        precalculated_val[1][1] = precalculated_val[0][1] * 10 + ((flop_table[ind / 2] >> ((ind & 0b1) << 2)) & 0b1111);
        ind = index3(deck[4], deck[5], deck[6]) * 1176 + hand_2;
        precalculated_val[1][2] = precalculated_val[0][2] * 10 + ((flop_table[ind / 2] >> ((ind & 0b1) << 2)) & 0b1111);

        if (deck[6] > deck[7]) std::swap(deck[6], deck[7]);
        if (deck[5] > deck[6]) std::swap(deck[5], deck[6]);
        if (deck[4] > deck[5]) std::swap(deck[4], deck[5]);

        dec4(c11, deck[0], deck[7], deck[6], deck[5], deck[4]);
        dec4(c12, deck[1], deck[7], deck[6], deck[5], deck[4]);
        dec4(c21, deck[2], deck[7], deck[6], deck[5], deck[4]);
        dec4(c22, deck[3], deck[7], deck[6], deck[5], deck[4]);
        hand_1 = index2(c11, c12);
        hand_2 = index2(c21, c22);

        ind = index4(deck[4], deck[5], deck[6], deck[7]) * 1128 + hand_1;
        precalculated_val[2][1] =
                (precalculated_val[1][1] * 10 + ((turn_table[ind / 2] >> ((ind & 0b1) << 2)) & 0b1111)) % 100;
        ind = index4(deck[4], deck[5], deck[6], deck[7]) * 1128 + hand_2;
        precalculated_val[2][2] =
                (precalculated_val[1][2] * 10 + ((turn_table[ind / 2] >> ((ind & 0b1) << 2)) & 0b1111)) % 100;

        if (deck[7] > deck[8]) std::swap(deck[7], deck[8]);
        if (deck[6] > deck[7]) std::swap(deck[6], deck[7]);
        if (deck[5] > deck[6]) std::swap(deck[5], deck[6]);
        if (deck[4] > deck[5]) std::swap(deck[4], deck[5]);

        dec5(c11, deck[0], deck[8], deck[7], deck[6], deck[5], deck[4]);
        dec5(c12, deck[1], deck[8], deck[7], deck[6], deck[5], deck[4]);
        dec5(c21, deck[2], deck[8], deck[7], deck[6], deck[5], deck[4]);
        dec5(c22, deck[3], deck[8], deck[7], deck[6], deck[5], deck[4]);
        hand_1 = index2(c11, c12);
        hand_2 = index2(c21, c22);

        ind = index5(deck[4], deck[5], deck[6], deck[7], deck[8]) * 1081 + hand_1;
        precalculated_val[3][1] =
                (precalculated_val[2][1] * 10 + ((river_table[ind / 2] >> ((ind & 0b1) << 2)) & 0b1111)) % 100;
        ind = index5(deck[4], deck[5], deck[6], deck[7], deck[8]) * 1081 + hand_2;

        precalculated_val[3][2] =
                (precalculated_val[2][2] * 10 + ((river_table[ind / 2] >> ((ind & 0b1) << 2)) & 0b1111)) % 100;

        u0 = HR[53 + deck[4] + 1];
        u0 = HR[u0 + deck[5] + 1];
        u0 = HR[u0 + deck[6] + 1];
        u0 = HR[u0 + deck[7] + 1];
        u0 = HR[u0 + deck[8] + 1];
        precalculated_val[4][1] = HR[HR[u0 + deck[0] + 1] + deck[1] + 1];
        precalculated_val[4][2] = HR[HR[u0 + deck[2] + 1] + deck[3] + 1];
//        printf("deck: %llu %llu %llu %llu %llu %llu %llu %llu %llu\n", deck[0], deck[1], deck[2], deck[3], deck[4],
//               deck[5],
//               deck[6], deck[7], deck[8]);
//        printf("p1 hand: %c%c %c%c\n", RANKS[deck[0] / 4], SUITS[deck[0] % 4], RANKS[deck[1] / 4], SUITS[deck[1] % 4]);
//        printf("p2 hand: %c%c %c%c\n", RANKS[deck[2] / 4], SUITS[deck[2] % 4], RANKS[deck[3] / 4], SUITS[deck[3] % 4]);
//        printf("board: %c%c %c%c %c%c %c%c %c%c\n", RANKS[deck[4] / 4], SUITS[deck[4] % 4], RANKS[deck[5] / 4],
//               SUITS[deck[5] % 4], RANKS[deck[6] / 4], SUITS[deck[6] % 4], RANKS[deck[7] / 4], SUITS[deck[7] % 4],
//               RANKS[deck[8] / 4], SUITS[deck[8] % 4]);
//
//        printf("evals: %llu %llu %llu %llu %llu %llu %llu %llu\n", precalculated_val[0][1], precalculated_val[0][2],
//               precalculated_val[1][1], precalculated_val[1][2], precalculated_val[2][1], precalculated_val[2][2],
//               precalculated_val[3][1], precalculated_val[3][2]);
//        printf("eval: %llu %llu\n", precalculated_val[4][1] >> 12, precalculated_val[4][2] >> 12);
        for (int j = 1; j <= 2; ++j) {
            cfr(0, nullptr, precalculated_val, nullptr, j, id);
        }
    }
    return nullptr;
}

void load_file() {
    total_regret = (double *) malloc(STRATEGY_SIZE * sizeof(double));
    total_strategy = (double *) malloc(STRATEGY_SIZE * sizeof(double));

    FILE *fin = fopen("contributions_big.dat", "rb");
    fread(contributions, sizeof(contributions), 1, fin);
    fclose(fin);
    fin = fopen("children_big.dat", "rb");
    fread(child, sizeof(child), 1, fin);
    fclose(fin);
    fin = fopen("player_at_state_big.dat", "rb");
    fread(player_at_state, sizeof(player_at_state), 1, fin);
    fclose(fin);
    fin = fopen("strategy_offset_big.dat", "rb");
    fread(strategy_offset, sizeof(strategy_offset), 1, fin);
    fclose(fin);

    fin = fopen("RiverClusters.dat", "rb");
    fread(river_table, sizeof(river_table), 1, fin);
    fclose(fin);
    fin = fopen("TurnClusters.dat", "rb");
    fread(turn_table, sizeof(turn_table), 1, fin);
    fclose(fin);
    fin = fopen("FlopClusters.dat", "rb");
    fread(flop_table, sizeof(flop_table), 1, fin);
    fclose(fin);

    HR = (int *) malloc(32487834 * sizeof(int));
    printf("Loading HandRanks.DAT file...");
    fin = fopen("HandRanks.dat", "rb");
    if (!fin) return;
    size_t bytesread = fread(HR, 32487834 * sizeof(int), 1, fin);    // get the HandRank Array
    fclose(fin);
    printf("complete.\n\n");
}


int main() {
//    printf("%llu", sizeof(total_regret) + sizeof(total_strategy) + sizeof(next_regret) + sizeof(next_strategy) +
//                   sizeof(strategy_offset) +
//                   sizeof(child) + sizeof(player_at_state) + sizeof(contributions) + sizeof(flop_table) +
//                   sizeof(preflop_table) +
//                   sizeof(turn_table) + sizeof(river_table) + sizeof(HR));
    setbuf(stdout, NULL);
    load_file();

    int id[THREADS];
    for (int i = 0; i < THREADS; ++i) {
        id[i] = i;
    }
    for (int i = 0; i < THREADS; ++i) {
        next_regret[i] = (volatile double *) (malloc(STRATEGY_SIZE * sizeof(double)));
        next_strategy[i] = (volatile double *) (malloc(STRATEGY_SIZE * sizeof(double)));

        for (int j = 0; j < STRATEGY_SIZE; ++j) {
            next_regret[i][j] = 0.0;
            next_strategy[i][j] = 0.0;
        }
    }
    pthread_t threads[THREADS];
    uint64_t iteration = 1;
    FILE *fin;
    while (1) {
        for (int i = 0; i < STRATEGY_SIZE; ++i) {
            total_regret[i] = 0.0;
            total_strategy[i] = 0.0;
        }
        for (int i = 0; i < THREADS; ++i) {
            for (int j = 0; j < STRATEGY_SIZE; ++j) {
                total_regret[j] += next_regret[i][j];
                total_strategy[j] += next_strategy[i][j];
            }
        }
        printf("iteration: %lu\n", iteration);
        for (int i = 0; i < THREADS; ++i) {
            pthread_create(&threads[i], nullptr, thread_handler, &id[i]);
        }

        if (iteration % 60 == 0) {
            fin = fopen("strategy.dat", "wb");
            fwrite(total_strategy, STRATEGY_SIZE * sizeof(double), 1, fin);
            fclose(fin);

            fin = fopen("regret.dat", "wb");
            fwrite(total_regret, STRATEGY_SIZE * sizeof(double), 1, fin);
            fclose(fin);

            printf("written!\n");
        }
        for (int i = 0; i < THREADS; ++i) {
            pthread_join(threads[i], nullptr);
        }
        printf("done\n");
        iteration++;
    }
}
