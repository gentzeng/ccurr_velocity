from logging             import INFO
from pandas              import DataFrame, to_datetime
from blocksci            import Blockchain
from blocksci.cluster    import ClusterManager
from blocksci.heuristics import change
from multiprocessing     import Pool, Lock, Value, cpu_count
from colorstrings        import ColorStrings as cs
from datetime            import date, datetime, timedelta
from math                import floor, ceil
from numpy               import cumsum
from itertools           import chain as it_chain
from more_itertools      import sort_together
from copy                import deepcopy

lock = Lock()

cluster_max_size_global = Value('i', 0)
cluster_max_id_global   = Value('i', 0)

def cls_worker(cls_range):
    cluster_max_size_local = 0
    cluster_max_id_local   = 0
    # skip assumingly max cluster, since its computation lasts to long
    arg_id, begin, end = cls_range

    for cluster_i in range(begin, end):
        if cluster_i == 32:
            continue;
        cluster_size = Velo.cluster_range[cluster_i].size()
        cluster_id   = Velo.cluster_range[cluster_i].index

        if cluster_i % 1000000 == 0:
            Velo.logger.info("{}[{}clustering     {}]{}  {}".format(
                cs.RES,
                cs.PRGnBA,
                cs.RES,
                cs.PRGnBA,

                "{:3}: [{:9}/{:9}]".format(
                    arg_id,
                    cluster_i,
                    end,
                ),
            ))

        if cluster_size > cluster_max_size_local:
            cluster_max_size_local = cluster_size
            cluster_max_id_local   = cluster_i
            if Velo.cluster_range[cluster_i].size() > 999:
                Velo.logger.info("{}[{}  clustering   {}]{}  {}".format(
                    cs.RES,
                    cs.PRGnBA,
                    cs.RES,
                    cs.PRGnBA,

                    "{:3}: [{:9}/{:9}] index/size = {:9}/{:6}{}".format(
                        arg_id,
                        cluster_i,
                        end,
                        cluster_max_id_local,
                        cluster_max_size_local,
                        "---new found",
                    ),
                ))

    Velo.logger.info("{}[{}  clustering   {}]{}  {}".format(
        cs.RES,
        cs.PRGnBA,
        cs.RES,
        cs.PRGnBA,

        "{:3}: [{:9}/{:9}] index/size = {:9}/{:6}{}".format(
            arg_id,
            cluster_i,
            end,
            cluster_max_id_local,
            cluster_max_size_local,
            "===finished",
        ),
    ))

    with lock:
        if cluster_max_size_local > cluster_max_size_global.value:
            cluster_max_size_global.value = cluster_max_size_local
            cluster_max_id_global.value   = cluster_max_id_local

    return

class Velo:
    """
    This class provides functionality to:
    - retrieve basic blockchain data, e.g., transaction volume
    - calculate transaction volume selfchurn via clustering of addresses
    - sophisticated measurements for money supply in circulation
    - eventually, measurements for the velocity of money in utxo-based crypto-
      currencies
    """

    #--class attribute representing blocksci chain object used by all instances-
    chain             = None              # the mainly blockcain object---------
    cluster_mgr       = None              # manager for clustering addresses----
    cluster_cnt       = None              # number of address clusters----------
    cluster_range     = None              # ------------------------------------
    cluster_max_id    = None              # id of cluster with max address count
    cluster_overwrite = False             # toggle overwriting of cluster cache-
    cluster_skip      = True              # skip recounting of cluster addresses
    block_times       = None              # ------------------------------------
    heur_select       = None              # selected change address heuristics--
    start             = None              # ------------------------------------
    end               = None              # ------------------------------------

    #--chosen columnnames for final dataframe-----------------------------------
    results_raw_types_basic        = None
    results_raw_types_tx_vol       = None
    results_raw_types_tx_vol_tw    = []
    results_raw_types_m_total      = None
    results_raw_types_m_circ       = None
    results_raw_types_m_circ_tw    = []
    results_raw_types_comp_meas    = None
    results_raw_types_comp_meas_tw = []

    #--lookup functions/mappings-(as lists)-------------------------------------
    f_index_day_of_bl_height     = []         # f_index-day(block height)-------
    f_bl_height_min_of_index_day = []         # f_bl_height_min(index_day)------
    f_bl_height_max_of_index_day = []         # f_bl_height_max(index_day)------
    f_dates_of_id_sub_proc       = []         # f_dates(subprocess-id)----------
    f_m_total_of_bl_height       = None       # f_m-total(block height)---------

    #--remaining class attributes-----------------------------------------------
    args              = None                  # commandline arguments-----------
    date_format       = "%Y-%m-%d %H:%M:%S"   # date formatting information-----
    start_date_gen    = "01/03/2009"          # date of bitcoin genesis---------
    path_data_output  = None                  # path for data output------------
    log_level         = INFO                  # default logging level-----------
    logger            = None                  # logging object------------------
    test_level        = 0                     # default basic test level-------
    process_cnt       = 0                     # count of sub procs for printing-
    cnt_days          = 0                     # count of days in range to be----
                                              # analyzed------------------------
    bl_height_max  = 0                        # maximum block height regarding--
                                              # given end date for analysis-----
    tx_vol_agg        = None                  # helper: daily aggr. tx volume---
    m_supply_add_a    = None                  # helper: money supply agg 1st add
    m_supply_add_b    = None                  # helper: money supply agg 2nd add
    m_supply_agg      = None                  # helper: money supply agg target-
    m_supply_cbs      = None                  # helper: money supply coinbased--
    tx_vol_churn_agg  = None                  # daily aggr. selfchurning tx vol-
    secs_per_day      = 86400                 # seconds per day 24*60*60--------

    #==[ CLASSLEVEL | SessionSetup & precaching of global data struct ]=========
    def setup(
        logger,
        args,
     ):
        """
        Initialize session and with that, the main blockchain object used by
        each instance of the Velo class.
        """
        def setup_chain_and_attributes(args):
            """
            This function handles the necessary commandline arguments for Velo
            and sets up static variables on class level.
            """
            #--setup of static variables on class level-------------------------
            Velo.args             = args
            Velo.test_level       = int(args.test_level)
            Velo.time_windows     = list(
                map(int, str(args.time_window).split(","))
            )
            Velo.cnt_cls_only     = args.count_clustering_only
            Velo.path_data_output = args.path_data_output
            Velo.chain            = Blockchain(args.path_data_input)

            Velo.start_date       = args.start_date
            if Velo.test_level > 0:
                Velo.end_date = "01/01/2012"
            else:
                Velo.end_date = args.end_date

            return

        def setup_logging(logger):
            """
            Setup logging and print basic info.
            """
            Velo.logger    = logger
            Velo.log_level = args.log_level

            #--print basic data in debug mode-----------------------------------
            Velo.logger.debug(
                "{}[{}value          {}]   {}   {}".format(
                    cs.RES,
                    cs.CYA,
                    cs.RES,
                    "{}[block_date 1st ]".format(cs.WHI),
                    "{}{}".format(
                        cs.WHI,
                        Velo.chain[0].time,
                    )
                )
            )
            Velo.logger.debug(
                "{}[{}value          {}]   {}   {}".format(
                    cs.RES,
                    cs.CYA,
                    cs.RES,
                    "{}[block_date last]".format(cs.WHI),
                    "{}{}".format(
                        cs.WHI,
                        Velo.chain[-1].time,
                    )
                )
            )

            return

        def setup_final_data_columns_choice():
            """
            This functions sets up the data choice for the final results.
            """
            # print status message----------------------------------------------
            Velo.logger.info(
                "{}[{}SETUP          {}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBA,
                    cs.RES,
                    "                 ",
                    "{}choice of desired data".format(cs.PRGnBA),
                )
            )

            # basic data from blockchain----------------------------------------
            Velo.results_raw_types_basic = [
                "index_day",
                "tx_count",
                "tx_fees",
            ]

            # transaction volume types   ---------------------------------------
            Velo.results_raw_types_tx_vol = [
                "tx_vol",
                "tx_vol_churn",
            ]

            for type in Velo.results_raw_types_tx_vol:
                for t_w in Velo.time_windows:
                    Velo.results_raw_types_tx_vol_tw.append(
                        "{}_{}".format(
                            type,
                            t_w,
                        )
                    )

            # money supply, total-----------------------------------------------
            Velo.results_raw_types_m_total = ["m_total"]

            # money supply in effective circulation-----------------------------
            Velo.results_raw_types_m_circ = [
                "m_circ_wh_bill",
                "m_circ_mc_lifo",
                "m_circ_mc_fifo",
                "outs_spent_btw",
            ]

            for type in Velo.results_raw_types_m_circ:
                for t_w in Velo.time_windows:
                    # do not include outs_spend_btw for a window size of one day
                    if t_w == 1 and type == "outs_spent_btw":
                        continue

                    Velo.results_raw_types_m_circ_tw.append(
                        "{}_{}".format(
                            type,
                            t_w,
                        )
                    )

            # compeating measurements for comparision---------------------------
            Velo.results_raw_types_comp_meas = [
                "sdd",
                "dormancy",
            ]

            for type in Velo.results_raw_types_comp_meas:
                for t_w in Velo.time_windows:
                    Velo.results_raw_types_comp_meas_tw.append(
                        "{}_{}".format(
                            type,
                            t_w,
                        )
                    )

            return

        def setup_heuristics():
            """
            compare
            https://citp.github.io/BlockSci/reference/heuristics/change.html
            Returns heuristics dictionary of selected heuristics
            """
            # print status message----------------------------------------------
            Velo.logger.info(
                "{}[{}SETUP          {}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBA,
                    cs.RES,
                    "                 ",
                    "{}change address heuristics".format(cs.PRGnBA),
                )
            )

            # setup heuristic lookup dictionary ids with heuristic names--------
            heur_names = [
                "address_reuse",
                "address_type",
                "client_change_address_behavior",
                "legacy",
                "legacy_improved",
                "peeling_chain",
                "locktime",
                "optimal_change",
                "power_of_ten_value"
            ]

            # setup heuristic lookup dictionary items---------------------------
            heur_items = []
            heur_items.append(change.address_reuse())
            heur_items.append(change.address_type())
            heur_items.append(change.client_change_address_behavior())
            heur_items.append(change.legacy())
            heur_items.append(change.legacy().__or__(change.peeling_chain()))
            heur_items.append(change.peeling_chain())
            heur_items.append(change.locktime())
            heur_items.append(change.optimal_change())
            heur_items.append(change.power_of_ten_value())

            # setup actual heuristic lookup dictionary--------------------------
            heur = dict(zip(heur_names, heur_items))
            Velo.heur_select = heur[Velo.args.heur_choice]

            return

        def setup_m_total_of_bl_height():
            """
            Precompute aggregated total money supply
            aka. cumulated coin supply for whole chain.
            """
            def coin_supply_renumeration(bl_height):
                """
                supply calculation of BTC inspired by:
                [https://www.coindesk.com/making-sense-bitcoins-halving/]
                """

                # the mining reward will be halved each 210000 blocks-----------
                halving_interval = 210000

                #initial reward
                reward = 50*100000000

                if bl_height < halving_interval:
                    return(reward)

                halvings = floor(bl_height / halving_interval)

                if halvings >= 64:
                    # (right shifting on 64 bit integer is be undefined then)
                    return(0)

                #using right shifts to devide by 2------------------------------
                reward >>= halvings

                return(reward)

            # print status message----------------------------------------------
            Velo.logger.info(
                "{}[{}SETUP          {}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBA,
                    cs.RES,
                    "                 ",
                    "{}calculating cumulative coin supply".format(cs.PRGnBA)
                )
            )

            # get basic values--------------------------------------------------
            last_block = Velo.chain[-1]
            bl_height_range_max = last_block.height

            # compute coin supply per block height------------------------------
            coin_supply_per_bl_height = []
            bl_height_range_max += 1

            for bl_height in range(0, bl_height_range_max):
                coin_supply_per_bl_height.append(
                    coin_supply_renumeration(bl_height)
                )

            # compute cumulated/aggregated coin supply per block height---------
            Velo.f_m_total_of_bl_height = cumsum(
                coin_supply_per_bl_height
            )

            return

        def setup_clustering_count():
            """
            Count addresses per cluster and retrieve id and size of biggest
            cluster.
            """
            #--print status message---------------------------------------------
            Velo.logger.info(
                "{}[{}SETUP          {}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBA,
                    cs.RES,
                    "                 ",
                    "{}clustering: get id of maximum cluster".format(cs.PRGnBA),
                )
            )

            #-------------------------------------------------------------------
            path_cluster          = Velo.args.path_cluster
            Velo.cluster_max_size = 0
            Velo.cluster_max_id   = 0

            # load blocksci clustering manager----------------------------------
            Velo.cluster_mgr = ClusterManager(
                path_cluster,
                Velo.chain,
            )

            # return assumingly largest cluster (id = 32), when skip is on------
            if True == Velo.cluster_skip:
                Velo.cluster_max_id = 32
                Velo.logger.info("{}[{}clustering     {}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBA,
                    cs.RES,
                    "                 ",
                    "{}Actually used max cluster: (with id/length {}/{})".format(
                        cs.PRGnBA,
                        Velo.cluster_max_id,
                        Velo.cluster_max_size,
                    ),
                ))

                if Velo.cnt_cls_only != 0:
                    exit(0)

                return

            # renew clustering cache, if desired--------------------------------
            if Velo.cluster_overwrite == True:
                Velo.cluster_mgr = ClusterManager.create_clustering(
                     path_cluster,
                     Velo.chain,
                     Velo.heur_select,
                     Velo.cluster_overwrite,
                )

            #--get largest cluster via subproccesing----------------------------
            Velo.cluster_range = Velo.cluster_mgr.clusters()
            Velo.cluster_cnt   = len(Velo.cluster_range)
            sub_proc_cls_range = ceil(Velo.cluster_cnt/cpu_count())

            Velo.logger.info(
                "{}[{}clustering     {}]"
                "{}  Number of clusters per subprocess/in total: {}/{}".format(
                    cs.RES,
                    cs.PRGnBA,
                    cs.RES,
                    cs.PRGnBA,
                    sub_proc_cls_range,
                    Velo.cluster_cnt
                )
            )

            # setup cluster address counting subprocesses-----------------------
            cls_args = []
            begin    = 0
            end      = 0
            for cpu_i in range (0, cpu_count()):
                begin = sub_proc_cls_range * cpu_i
                end   = sub_proc_cls_range * (cpu_i+1) - 1

                if end > Velo.cluster_cnt:
                    end = Velo.cluster_cnt -1

                cls_arg = (cpu_i, begin, end)
                cls_args.append(cls_arg)

            # start subproccesing-----------------------------------------------
            p = Pool(cpu_count())
            p.map(cls_worker, cls_args)

            # retrieve results--------------------------------------------------
            Velo.cluster_max_id   = cluster_max_id_global.value
            Velo.cluster_max_size = cluster_max_size_global.value

            # Hardcoded result. Only change if parsing/clustering changes
            # Velo.cluster_max_id = 32

            Velo.logger.info("{}[{}clustering     {}]{}  {}".format(
                cs.RES,
                cs.PRGnBA,
                cs.RES,
                cs.PRGnBA,
                "Finished (largest cluster id/size {}/{})".format(
                    Velo.cluster_max_id,
                    Velo.cluster_max_size,
                ),
            ))

            # check whether we only want to count cluster addresses-------------
            if Velo.cnt_cls_only != 0:
                exit(0)

            return

        def setup_subprocessing_chunks():
            """
            Setup transactions chunks for multiprocessing.
            """
            def setup_subprocessing_chunks_per_day(
                day,
                sub_proc_tx_cnt_max,
                sub_proc_txes_counter,
                sub_proc_date_start,
                sub_proc_date_end,
                sub_proc_date_period,
                cnt_txes_per_day,
                sub_proc_printed,
            ):
                """
                Setup transactions chunks for multiprocessing per day.
                """
                # Assumption: There is no day with cnt_txes > sub_proc_tx_cnt_max

                # txes numbers of all other days
                txes_counter_next = sub_proc_txes_counter + cnt_txes_per_day

                #if txes_counter_next < sub_proc_tx_cnt_max or sub_proc_printed == cpu_count()-1:
                sub_proc_date_end    += timedelta(days = 1)
                sub_proc_date_period += 1
                sub_proc_txes_counter = txes_counter_next

                if txes_counter_next < sub_proc_tx_cnt_max:
                    #sub_proc_date_end    += timedelta(days = 1)
                    #sub_proc_date_period += 1
                    #sub_proc_txes_counter = txes_counter_next
                    pass

                else:
                    sub_proc_date = [
                        sub_proc_date_start,
                        sub_proc_date_end,
                        sub_proc_date_period,
                        sub_proc_txes_counter
                    ]
                    Velo.f_dates_of_id_sub_proc.append(sub_proc_date)
                    Velo.logger.info(
                        "{}[{}process_{:03}    {}]   {}   {}".format(
                            cs.RES,
                            cs.PRGnBA,
                            sub_proc_printed,
                            cs.RES,
                            "{}{:6}     {:6}".format(
                                cs.WHI,
                                day+1-sub_proc_date_period,
                                sub_proc_date_period,
                            ),
                            "{}--{}   {:10}".format(
                                datetime.strftime(
                                    sub_proc_date_start,
                                    "%Y/%m/%d",
                                ),
                                datetime.strftime(
                                    sub_proc_date_end,
                                    "%Y/%m/%d",
                                ),
                                sub_proc_txes_counter,
                            ),
                        )
                    )
                    sub_proc_printed     += 1
                    sub_proc_date_start   = sub_proc_date_end
                    sub_proc_date_end     = sub_proc_date_start
                    sub_proc_date_period  = 0
                    sub_proc_txes_counter = 0
                    #sub_proc_txes_counter = cnt_txes_per_day

                # treat last day seperately-------------------------------------
                if day == (Velo.cnt_days-1):
                    sub_proc_date = [
                        sub_proc_date_start,
                        sub_proc_date_end,
                        sub_proc_date_period,
                        sub_proc_txes_counter
                    ]
                    Velo.f_dates_of_id_sub_proc.append(sub_proc_date)
                    Velo.logger.info(
                        "{}[{}process_{:03}    {}]   {}   {}".format(
                            cs.RES,
                            cs.PRGnBA,
                            sub_proc_printed,
                            cs.RES,
                            "{}{:6}     {:6}".format(
                                cs.WHI,
                                day+1-sub_proc_date_period,
                                sub_proc_date_period,
                            ),
                            "{}--{}   {:10}".format(

                                datetime.strftime(
                                    sub_proc_date_start,
                                    "%Y/%m/%d",
                                ),
                                datetime.strftime(
                                    sub_proc_date_end,
                                    "%Y/%m/%d",
                                ),
                                sub_proc_txes_counter,
                            ),
                        )
                    )

                return (
                    sub_proc_printed,
                    sub_proc_txes_counter,
                    sub_proc_date_start,
                    sub_proc_date_end,
                    sub_proc_date_period
                )

            #--print status message---------------------------------------------
            Velo.logger.info(
                "{}[{}SETUP          {}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBA,
                    cs.RES,
                    "                 ",
                    "{}subprocessing chunks of blockchain".format(cs.PRGnBA),
                )
            )

            #--get block times and day counts-----------------------------------
            Velo.block_times = DataFrame(
                [block.time for block in Velo.chain],
                columns = ["date"],
            )
            Velo.block_times["height"] = Velo.block_times.index
            Velo.block_times.index     = Velo.block_times["date"]
            del Velo.block_times["date"]

            Velo.cnt_days = (
                to_datetime(Velo.end_date) - to_datetime(Velo.start_date_gen)
            ).days

            # print number of days
            Velo.logger.debug(
                "{}[{}value          {}]   {}   {}".format(
                    cs.RES,
                    cs.CYA,
                    cs.RES,
                    "{}[number of days ]".format(cs.WHI),
                    "{}{:10}".format(
                        cs.WHI,
                        Velo.cnt_days,
                    )
                )
            )

            #--get minimum/maximum bl_height according to start/end_date-----
            bl_height_min = Velo.block_times[
                Velo.block_times.index >= to_datetime(Velo.start_date_gen)
            ].iloc[0][0]

            bl_height_max = Velo.block_times[
                Velo.block_times.index >= to_datetime(Velo.end_date)
            ].iloc[0][0]

            Velo.bl_height_max = bl_height_max

            #--get transcation counts between start/end_date blocks-------------
            cnt_txes = 0
            for i_bh in range(bl_height_min, bl_height_max):
                cnt_txes += Velo.chain[i_bh].tx_count

            # print number of txes
            Velo.logger.debug(
                "{}[{}value          {}]   {}   {}".format(
                    cs.RES,
                    cs.CYA,
                    cs.RES,
                    "{}[number of txes ]".format(cs.WHI),
                    "{}{:10}".format(
                        cs.WHI,
                        cnt_txes,
                    )
                )
            )

            # print number of cpus----------------------------------------------
            Velo.logger.debug(
                "{}[{}value          {}]   {}   {}".format(
                    cs.RES,
                    cs.CYA,
                    cs.RES,
                    "{}[number of cpus ]".format(cs.WHI),
                    "{}{:10}".format(
                        cs.WHI,
                        cpu_count(),
                    )
                )
            )

            #-initialize data for subprocessing---------------------------------
            day_date              = to_datetime(Velo.start_date_gen)
            day_date_next         = day_date
            sub_proc_tx_cnt_max   = ceil(cnt_txes/cpu_count())
            sub_proc_txes_counter = 0
            sub_proc_date_start   = day_date
            sub_proc_date_end     = day_date + timedelta(days=1)
            sub_proc_date_period  = 1
            sub_proc_printed      = 0

            Velo.logger.info(
                "{}[{}assign periods {}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBA,
                    cs.RES,
                    "{}day_id      #days".format(cs.PRGnBA),
                    "        period                #txes"
                )
            )

            for day in range(Velo.cnt_days):
                # update for-loop date variables--------------------------------
                day_date       = day_date_next
                day_date_next += timedelta(days=1)

                # initialize for-scope variables--------------------------------
                cnt_txes_per_day = 0

                # get minimum and maximum block height according to actual day--
                bl_height_min = Velo.block_times[
                    Velo.block_times.index >= day_date
                ].iloc[0][0]

                bl_height_max = Velo.block_times[
                    Velo.block_times.index >= day_date_next
                ].iloc[0][0]

                Velo.f_bl_height_min_of_index_day.append(bl_height_min)
                Velo.f_bl_height_max_of_index_day.append(bl_height_max-1)

                # retrieve values per block in daily blockrange-----------------
                for i_bh in range(bl_height_min, bl_height_max):
                    cnt_txes_per_day += Velo.chain[i_bh].tx_count

                    Velo.f_index_day_of_bl_height.append(day)

                # calculate data for sub processing periods---------------------
                if day == 0:
                    # txes number of first day, don't change dates
                    sub_proc_txes_counter = cnt_txes_per_day

                else:
                    ret = setup_subprocessing_chunks_per_day(
                        day,
                        sub_proc_tx_cnt_max,
                        sub_proc_txes_counter,
                        sub_proc_date_start,
                        sub_proc_date_end,
                        sub_proc_date_period,
                        cnt_txes_per_day,
                        sub_proc_printed,
                    )

                    sub_proc_printed      = ret[0]
                    sub_proc_txes_counter = ret[1]
                    sub_proc_date_start   = ret[2]
                    sub_proc_date_end     = ret[3]
                    sub_proc_date_period  = ret[4]

            return

        #--setup of static variables on class level-----------------------------
        setup_chain_and_attributes(args)

        #--setup logging--------------------------------------------------------
        setup_logging(logger)

        #--setup names of resulting data----------------------------------------
        setup_final_data_columns_choice()

        #--setup heurictics object----------------------------------------------
        setup_heuristics()

        #--setup clustering object----------------------------------------------
        setup_clustering_count()

        #--setup total amount of money supply-----------------------------------
        setup_m_total_of_bl_height()

        #--setup data for subprocessing-----------------------------------------
        setup_subprocessing_chunks()

        return

    #==[ CLASSLEVEL | finalize results and get final data frames and csv ]======
    def get_results_finalized(
        results_raw,
        index_label = "",
    ):
        """
        Builds a pandas data frame and csv from pre-computed data.
        """
        def agg_time_windowed_tx_vol(results_raw):
            """
            Compute transaction volume aggregates for given times in
            Velo.time_windows.
            """
            def agg_time_windowed_tx_vol_per_day(
                    day,
                    tx_vol_agg_nxt_day,
                    tx_vol_churn_agg_nxt_day,
            ):
                """
                Compute daily transaction volume aggregates for given times in
                Velo.time_windows.
                """
                for t_w in range(1, len(Velo.time_windows)):
                    tx_vol_agg_last       = 0
                    tx_vol_churn_agg_last = 0

                    # get the previously computed window------------------------
                    if day > 0:
                        tx_vol_agg_last       = Velo.tx_vol_agg[t_w][day-1]
                        tx_vol_churn_agg_last = Velo.tx_vol_churn_agg[t_w][day-1]

                    #-add the current daily calculations------------------------
                    tx_vol_agg_tw       = tx_vol_agg_last + tx_vol_agg_nxt_day
                    tx_vol_churn_agg_tw = (
                        tx_vol_churn_agg_last + tx_vol_churn_agg_nxt_day
                    )

                    #-substract the calculations right before the new window----
                    if day >= Velo.time_windows[t_w]:
                        day_sub = day - Velo.time_windows[t_w]

                        tx_vol_agg_tw       -= Velo.tx_vol_agg[0][day_sub]
                        tx_vol_churn_agg_tw -= Velo.tx_vol_churn_agg[0][day_sub]

                    Velo.tx_vol_agg[t_w]      .append(tx_vol_agg_tw)
                    Velo.tx_vol_churn_agg[t_w].append(tx_vol_churn_agg_tw)

                return

            #--print status message---------------------------------------------
            Velo.logger.info(
                "{}[{}Aggregate      {}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBI,
                    cs.RES,
                    "                 ",
                    "{}windowed tx volume".format(cs.PRGnBI),
                )
            )
            #-------------------------------------------------------------------
            time_windows          = Velo.time_windows
            time_windows_cnt      = len(time_windows)
            tx_vol                = results_raw["tx_vol_1"]
            tx_vol_churn          = results_raw["tx_vol_churn_1"]
            Velo.tx_vol_agg       = [[] for t in range(time_windows_cnt)]
            Velo.tx_vol_churn_agg = [[] for t in range(time_windows_cnt)]

            # aggreation steps per day------------------------------------------
            for day in range(Velo.cnt_days):
                tx_vol_day       = tx_vol[day]
                tx_vol_churn_day = tx_vol_churn[day]

                Velo.tx_vol_agg[0]      .append(tx_vol_day)
                Velo.tx_vol_churn_agg[0].append(tx_vol_churn_day)

                # aggregate txes volume for given time windows------------------
                agg_time_windowed_tx_vol_per_day(
                    day,
                    tx_vol_day,
                    tx_vol_churn_day,
                )

            # prepare return----------------------------------------------------
            for t_w in range(1, time_windows_cnt):
                tx_vol_key       = "tx_vol_{}"      .format(time_windows[t_w])
                tx_vol_churn_key = "tx_vol_churn_{}".format(time_windows[t_w])
                results_raw[tx_vol_key]       = Velo.tx_vol_agg[t_w]
                results_raw[tx_vol_churn_key] = Velo.tx_vol_churn_agg[t_w]

            return results_raw

        def agg_time_windowed_m_supply(results_raw):
            """
            Compute money supply aggregates for given times in
            Velo.time_windows.
            """
            def agg_time_windowed_m_supply_per_day(day):
                """
                Compute daily money supply aggregates for given times in
                Velo.time_windows.
                """
                for t_w in range(1, len(Velo.time_windows)):
                    m_supply_agg_last = 0
                    
                    wndw = Velo.time_windows[t_w]

                    # get the previously computed window------------------------
                    if day > 0:
                        m_supply_agg_last = Velo.m_supply_agg[t_w][day-1]

                    #-add the current daily calculations------------------------
                    m_supply_agg_tw = m_supply_agg_last
                    if day < wndw:
                    #if day >= wndw:
                        # no "spent last" transactions, only coinbase contribute
                        # to m_supply in circulation in first tw days
                        m_supply_agg_tw += Velo.m_supply_cbs[day]
                    else:
                        m_supply_agg_tw += Velo.m_supply_add_a[t_w][day]

                    #-substract the calculations right before the new window----
                    if day >= wndw:
                        day_sub = day - wndw

                        m_supply_agg_tw -= Velo.m_supply_add_a[0][day_sub]
                        m_supply_agg_tw += Velo.m_supply_add_b[t_w][day_sub]

                    Velo.m_supply_agg[t_w].append(m_supply_agg_tw)

                return

            #--print status message---------------------------------------------
            Velo.logger.info(
                "{}[{}Aggregate      {}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBI,
                    cs.RES,
                    "                 ",
                    "{}windowed money supply".format(cs.PRGnBI),
                )
            )
            #-------------------------------------------------------------------
            time_windows       = Velo.time_windows
            time_windows_cnt   = len(time_windows)
            m_supply_cbs_key   = "m_circ_cbs"
            m_supply_add_a_key = "m_circ_wh_bill"
            m_supply_add_b_key = "outs_spent_btw"
            m_supply_agg_key   = "m_circ_wh_bill"
            m_supply_add_a     = [[] for t in range(time_windows_cnt)]
            m_supply_add_b     = [[] for t in range(time_windows_cnt)]
            m_supply_agg       = [[] for t in range(time_windows_cnt)]

            # get sum and sub for aggregation------------------------
            for t_w in range(time_windows_cnt):
                m_supply_add_a_key_tw = "{}_{}".format(
                    m_supply_add_a_key,
                    time_windows[t_w],
                )
                m_supply_add_b_key_tw = "{}_{}".format(
                    m_supply_add_b_key,
                    time_windows[t_w],
                )

                m_supply_add_a[t_w] = results_raw[m_supply_add_a_key_tw]
                m_supply_add_b[t_w] = results_raw[m_supply_add_b_key_tw]

            Velo.m_supply_cbs   = results_raw[m_supply_cbs_key]
            Velo.m_supply_add_a = m_supply_add_a
            Velo.m_supply_add_b = m_supply_add_b
            Velo.m_supply_agg   = m_supply_agg

            # aggreation steps per day------------------------------------------
            for day in range(Velo.cnt_days):
                agg_time_windowed_m_supply_per_day(day)

            # prepare return----------------------------------------------------
            for t_w in range(1, time_windows_cnt):
                m_supply_agg_key_tw = "{}_{}".format(
                    m_supply_agg_key,
                    time_windows[t_w],
                )
                results_raw[m_supply_agg_key_tw] = Velo.m_supply_agg[t_w]

            return results_raw

        def get_comp_meas_finalized(
            results_raw,
            min_frac = 1,
        ):
            """
            Function using the results form get_comp_meas to
            aggregate them after their results have been joined after the
            threading. Here lastly the measures dormancy and
            satoshi days destroyed (ssd) are created.
            """

            def cumsum_with_window_reverse(
                l,
                window,
                min_frac = min_frac,
            ):
                """
                Sub-function that calculates the aggregate sum over the past
                window size. As our lists start with the earliest date, the
                lists are reversed and after the accumulation re-reversed.
                This makes sense, as we want the lookback window to look
                backwards and not in the future, so that we get missing values
                in the earliest dates.
                """

                #--reverse the list, as we need to start with the latest date---
                l.reverse()

                #--set minimum periods necessary for cumsum---------------------
                min_periods = int(window*min_frac)

                #--convert list to pandas df------------------------------------
                df = DataFrame(l)

                #--calculate cumsum with lookback window------------------------
                df = df.rolling(
                    window = window,
                    min_periods = min_periods,
                ).sum().shift(-(window-1))

                #--convert pandas df back to list-------------------------------
                l = list(it_chain(*df.values.tolist()))

                #--reverse the list to be starting with the earliest date-------
                l.reverse()

                return l

            #--print status message---------------------------------------------
            Velo.logger.info(
                "{}[{}Finalize       {}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBI,
                    cs.RES,
                    "                 ",
                    "{}dormancy".format(cs.PRGnBI),
                )
            )

            #-------------------------------------------------------------------
            time_windows     = Velo.time_windows
            time_windows_cnt = len(time_windows)

            # finalize dormancy per time window---------------------------------
            for day_i in range(Velo.cnt_days):
                for t_w in range(time_windows_cnt):
                    # initialize transaction volume per time window up to this--
                    # day
                    tx_vol_per_day = Velo.tx_vol_agg[t_w][day_i]

                    dormancy_tw_key = "dormancy_raw_{}".format(
                        time_windows[t_w]
                    )

                    if tx_vol_per_day == 0:
                        results_raw[dormancy_tw_key][day_i] = 0
                        continue

                    results_raw[dormancy_tw_key][day_i] /= tx_vol_per_day

            #-------------------------------------------------------------------
            for t_w in range(time_windows_cnt):
                satoshi_dd_tw_key = "sdd_{}".format(time_windows[t_w])
                dormancy_tw_key   = "dormancy_{}".format(time_windows[t_w])

                results_raw[satoshi_dd_tw_key] = cumsum_with_window_reverse(
                    l = list(
                        results_raw["sdd_raw_{}".format(time_windows[t_w])]
                    ),
                    window = 1,
                )

                results_raw[dormancy_tw_key] = cumsum_with_window_reverse(
                    l = list(
                        results_raw["dormancy_raw_{}".format(time_windows[t_w])]
                    ),
                    window = time_windows[t_w],
                )

            return

        def collect_daychunks(window_size):
            """
            """

            wndw = window_size
            bh_min = 0
            bh_max = 0

            daychunks = [[] for t in range(Velo.cnt_days)]

            for day in range(Velo.cnt_days):
                if day % 10 == 0:
                    Velo.logger.debug(
                        "aggr collect day {:4}/{:4}".format(
                            day,
                            Velo.cnt_days,
                        )
                    )
                if day < wndw:
                    bh_min = Velo.f_bl_height_min_of_index_day[0]
                else:
                    bh_min = Velo.f_bl_height_min_of_index_day[day-wndw+1]

                bh_max = Velo.f_bl_height_max_of_index_day[day]+1

                for i_bh in range(bh_min, bh_max):
                    for tx in Velo.chain[i_bh]:
                        daychunks[day].append(tx)

            return daychunks

        def m_circ_wh_bill_per_tx_test(
            tx,
            bl_height,
        ):
            """
            """
            def inp_spent_before_bh_or_coinbase_test(
                inp,
                bl_heights
            ):
                """
                This function represents the condition for the handle_tx_mc
                functions to decide, whether to sum an input or not.
                """

                inp_spent_index = 0
                is_coinbase     = False

                inp_spent_tx_bl_height = inp.spent_tx.block_height

                # check if the tx that spent this input is a coinbase tx----
                if inp.spent_tx.is_coinbase:
                    if inp_spent_tx_bl_height < bl_height or ( 0 == inp_spent_tx_bl_height and 0 == bl_height ):
                        inp_spent_index = 2
                    else:
                        inp_spent_index = 3
                    return inp_spent_index

                # if bl_height <= 0, we discard this input since it-----
                # cannot be spent before this block height
                if bl_height <= 0:
                    return 0

                # check if the tx that spent this input is older than given-
                # block height

                if inp_spent_tx_bl_height < bl_height:
                    inp_spent_index = 1

                return inp_spent_index

            m_circ_mc      = 0
            inps           = tx.inputs
            val_outs_break = 0
            val_outs       = tx.output_value
            bl_height_loc  = bl_height

            if tx.input_value == 0 or val_outs == 0 or tx.is_coinbase:
                return m_circ_mc

            else:
                # 1)
                val_outs_sent_to_others = val_outs + tx.fee

                # 2)
                if val_outs_sent_to_others < 0:
                    raise ValueError(
                        "val_outs_sent_to_others must not be less than 0!"
                    )
                elif val_outs_sent_to_others == 0:
                    return m_circ_mc

                # 4)
                for inp_i in inps:
                    val_inp_i = inp_i.value
                    val_outs_break += val_inp_i

                    inp_spent_index = inp_spent_before_bh_or_coinbase_test(
                        inp_i,
                        bl_height_loc,
                    )

                    if ( inp_spent_index ):
                        # if coinbase is within window, do not count fee
                        if ( 3 == inp_spent_index):
                            m_circ_mc += (
                                inp_i.spent_tx.block.revenue
                                - inp_i.spent_tx.block.fee
                            )
                        else:
                            m_circ_mc += val_inp_i

                        # **)
                        if val_outs_break >= val_outs_sent_to_others:
                            if m_circ_mc >= val_outs_sent_to_others:
                                m_circ_mc = val_outs_sent_to_others
                            break

            if m_circ_mc < 0:
                raise ValueError(
                    "m_circ_m must not be less than 0!"
                    )

            return m_circ_mc

        def m_circ_wh_bill_test(daychunks):
            """
            """
            m_circ_wh_bill_test = []

            for daychunk_i in range(len(daychunks)):
                if daychunk_i % 10 == 0:
                    Velo.logger.debug(
                        "aggr test day {:4}/{:4}".format(
                            daychunk_i,
                            len(daychunks),
                        )
                    )

                daychunk = daychunks[daychunk_i]
                m_circ_wh_bill_test.append(0)

                if daychunk == []:
                    continue

                bh_pre = daychunk[0].block_height

                for tx in daychunk:
                    if tx.output_value <= tx.fee:
                        continue

                    m_circ_wh_bill_test[-1] += m_circ_wh_bill_per_tx_test(
                        tx,
                        bh_pre
                    )

            return m_circ_wh_bill_test

        #--Start of get_results_finalized()-------------------------------------
        Velo.logger.debug(
            "{}[{}function       {}]   {}   {}".format(
                cs.RES,
                cs.CYA,
                cs.RES,
                "{}[Started        ]".format(cs.WHI),
                "Velo.get_results_finalized",
            )
        )

        #-aggregate transaction volume (e.g., for dormancy)-----------------
        results_raw["tx_vol_1"]       = results_raw.pop("tx_vol")
        results_raw["tx_vol_churn_1"] = results_raw.pop("tx_vol_churn")

        results_raw = agg_time_windowed_tx_vol(results_raw)
        results_raw_old = deepcopy(results_raw)

        #--aggregate money supply-------------------------------------------
        if len(Velo.time_windows) > 1:
            results_raw = agg_time_windowed_m_supply(results_raw)

        #--prepare measures to be compared with velocity------------------------
        get_comp_meas_finalized(
            results_raw=results_raw,
            min_frac = 1,
        )

        #--create first part of final pandas data frame-------------------------
        results_raw_basic = {
            k: results_raw[k]
            for k in Velo.results_raw_types_basic
        }
        df_final = DataFrame.from_dict(results_raw_basic)
        df_final = df_final.set_index("index_day")

        for m_circ_type in Velo.results_raw_types_m_circ_tw:
            df_final["{}_o".format(m_circ_type)] = results_raw_old[m_circ_type]

        #--handle m_circ_tests--------------------------------------------------
        daychunks = collect_daychunks(1)
        m_circ_wh_bill_raw_test = m_circ_wh_bill_test(daychunks)

        df_final["m_circ_cbs"] = results_raw["m_circ_cbs"]
        df_final["m_circ_test"] = m_circ_wh_bill_raw_test

        #--handle tv_vol df_types and merge to final data frame-----------------
        for tx_vol_type in Velo.results_raw_types_tx_vol_tw:
            df_final[tx_vol_type] = results_raw[tx_vol_type]

        #--handle m_total df_types and merge to final data frame----------------
        for m_total_type in Velo.results_raw_types_m_total:
            df_final[m_total_type] = results_raw[m_total_type]

        #--handle m_circ df_types and merge to final data frame-----------------
        for m_circ_type in Velo.results_raw_types_m_circ_tw:
            df_final[m_circ_type] = results_raw[m_circ_type]

        #--handle measurements from literature and merge to finale data frame---
        for comp_meas_type in Velo.results_raw_types_comp_meas_tw:
            df_final[comp_meas_type] = results_raw[comp_meas_type]

        #--print status message-------------------------------------------------
        Velo.logger.info("{}[{}built dataframe{}]   {}   {}".format(
            cs.RES,
            cs.PRGnBI,
            cs.RES,
            "                 ",
            "{}final dataframe".format(cs.PRGnBI),
        ))

        #--remove row from January 4th 2009 to January 8th 2009-----------------
        df_final = df_final.drop([
            '09/01/04',
            '09/01/05',
            '09/01/06',
            '09/01/07',
            '09/01/08',
        ])

        #--build final csv------------------------------------------------------
        now_date       = datetime.now()
        end_date_d     = datetime.strptime(Velo.end_date, "%m/%d/%Y").date()
        now_date_str   = now_date.strftime("%Y%m%d_%H%M")
        end_date_str   = end_date_d.strftime("%Y%m%d")
        path           = "{}_csv/".format(Velo.path_data_output)
        filename_dates = "{}{}_e_{}".format(path, now_date_str, end_date_str)
        filename       = "{}_{}.csv".format(filename_dates, "velo_daily")

        df_final.to_csv(
            filename,
            sep=",",
            header=True,
            date_format=Velo.date_format,
            index_label=index_label,
        )

        #--print status message-------------------------------------------------
        Velo.logger.info(
            "{}[{}wrote csv      {}]".format(
                cs.RES,
                cs.PRGnBI,
                cs.RES,
            )
        )
        Velo.logger.debug(
            "{}[{}function       {}]   {}   {}".format(
                cs.RES,
                cs.CYA,
                cs.RES,
                "{}[Finished       ]".format(cs.WHI),
                "Velo.get_results_finalized",
            )
        )

        return

    #--PUBLIC INSTANCE-LEVEL METHODS--##########################################
    #==[ INSTALEVEL | Initialize instances ]====================================
    def __init__ (
        self,
        process_id,
        process_name,
        queue,
        queue_evnt,
        date_id,
    ):
        """
        Initialize subprocess.
        """
        self.stage_id     = 0
        self.process_id   = process_id
        self.process_name = process_name
        self.__queue      = queue
        self.__queue_evnt = queue_evnt

        # next day to include date_period_end. Otherwise, it won't be regarded
        # due to the blocksci chainrange being computed as the daily difference.
        s_p_d = Velo.f_dates_of_id_sub_proc

        date_period_start        = s_p_d[date_id][0]
        date_period_end          = s_p_d[date_id][1] - timedelta(days=1)
        date_period              = s_p_d[date_id][2]
        self.__date_id           = date_id
        self.__date_period_start = date_period_start
        self.__date_period_end   = date_period_end
        self.__date_period       = date_period
        self.__start_date        = date_period_start.strftime("%m/%d/%y")
        self.__end_date          = date_period_end.strftime("%m/%d/%y")
        self.__end_date_next     = date_period_end + timedelta(days=1)

        # instance-wise interfunctional temporary helper stuctures--------------
        self.__txes_daily = None
        self.__txes_count = s_p_d[date_id][3]

        # data structures conveyed by subprocess queues-------------------------
        self.__queue_dict      = {}
        self.__queue_evnt_dict = {}

    #==[ INSTALEVEL | Retrieve of desired data ]================================
    def run(self):
        """
        Run the thread.
        """
        def print_liveliness_message(
            i_day,
            function_str,
        ):
            """
            This function checks whether a liveliness message regaring
            the number of txes and the respective day id should be
            printed.
            Note that this function is not very dynamic and totally
            uggly!
            """
            print_still_alive = False
            txes_num = self.__txes_count
            date_period = self.__date_period

            if date_period <= 25:
                if txes_num <= 125000:
                    if (i_day % 36) == 0:
                        print_still_alive = True
                elif txes_num <= 250000:
                    if (i_day % 24) == 0:
                        print_still_alive = True
                elif txes_num <= 500000:
                    if (i_day % 18) == 0:
                        print_still_alive = True
                elif txes_num <= 1000000:
                    if (i_day % 12) == 0:
                        print_still_alive = True
                elif txes_num <= 2000000:
                    if (i_day % 6) == 0:
                        print_still_alive = True
                elif txes_num <= 4000000:
                    if (i_day % 4) == 0:
                        print_still_alive = True
                else:
                    if (i_day % 2) == 0:
                        print_still_alive = True

            elif date_period <= 50:
                if txes_num <= 125000:
                    if (i_day % 72) == 0:
                        print_still_alive = True
                elif txes_num <= 250000:
                    if (i_day % 48) == 0:
                        print_still_alive = True
                elif txes_num <= 500000:
                    if (i_day % 36) == 0:
                        print_still_alive = True
                elif txes_num <= 1000000:
                    if (i_day % 24) == 0:
                        print_still_alive = True
                elif txes_num <= 2000000:
                    if (i_day % 12) == 0:
                        print_still_alive = True
                elif txes_num <= 4000000:
                    if (i_day % 8) == 0:
                        print_still_alive = True
                else:
                    if (i_day % 4) == 0:
                        print_still_alive = True

            elif date_period <= 100:
                if txes_num <= 125000:
                    if (i_day % 128) == 0:
                        print_still_alive = True
                elif txes_num <= 250000:
                    if (i_day % 96) == 0:
                        print_still_alive = True
                elif txes_num <= 500000:
                    if (i_day % 72) == 0:
                        print_still_alive = True
                elif txes_num <= 1000000:
                    if (i_day % 48) == 0:
                        print_still_alive = True
                elif txes_num <= 2000000:
                    if (i_day % 24) == 0:
                        print_still_alive = True
                elif txes_num <= 4000000:
                    if (i_day % 16) == 0:
                        print_still_alive = True
                else:
                    if (i_day % 8) == 0:
                        print_still_alive = True

            elif date_period <= 200:
                if txes_num <= 125000:
                    if (i_day % 256) == 0:
                        print_still_alive = True
                elif txes_num <= 250000:
                    if (i_day % 192) == 0:
                        print_still_alive = True
                elif txes_num <= 500000:
                    if (i_day % 144) == 0:
                        print_still_alive = True
                elif txes_num <= 1000000:
                    if (i_day % 96) == 0:
                        print_still_alive = True
                elif txes_num <= 2000000:
                    if (i_day % 48) == 0:
                        print_still_alive = True
                elif txes_num <= 4000000:
                    if (i_day % 32) == 0:
                        print_still_alive = True
                else:
                    if (i_day % 16) == 0:
                        print_still_alive = True

            elif date_period <= 1000:
                if txes_num <= 3_500_000:
                    if (i_day % 160) == 0:
                        print_still_alive = True
                else:
                    if (i_day % 80) == 0:
                        print_still_alive = True

            else:
                if txes_num <= 4_000_000:
                    if (i_day % 240) == 0:
                        print_still_alive = True
                else:
                    if (i_day % 120) == 0:
                        print_still_alive = True

            if i_day != 0 and print_still_alive == True:
                colorChoice = cs.WHI
                if date_period >= 100:
                    colorChoice = cs.CYB

                Velo.logger.info(
                    "{}[{}{}/{:03}{}]   {}   {}".format(
                        cs.RES,
                        colorChoice,
                        self.process_name,
                        Velo.process_cnt-1,
                        cs.RES,
                        "{}[day_{:05d}/{:05d}]".format(
                            cs.WHI,
                            i_day,
                            date_period,
                        ),
                        function_str,
                    ),
                )

            return

        def in_max_cluster(out):
            """
            This function checks whether a given output (out) belongs to the
            biggest cluster of the applied change heuristic.
            """

            out_addr   = out.address
            out_cls    = Velo.cluster_mgr.cluster_with_address(out_addr)
            out_cls_id = out_cls.index

            if Velo.cluster_max_id == out_cls_id:
                return True

            return False

        def get_basic_tx_data():
            """
            This function retrieves per subprocessing chunk:
            - txes_daily:       list of daily grouped txes
            - index_day:        index list of day ids
            - txes_count:       list of counted transactions per day
            - txes_fees:        list of aggregated transaction fees per day
            - txes_dust_fees:   list of aggregated transaction dust fees per day
            - txes_dust_inpval: list of aggregated transaction dust
                                input values per day
            - txes_vol:         transaction volume per day
                                (output values of transactions per day)
            - txes_vol_churn:   transaction volume selfchurn per day
                                (check our paper or blocksci paper)
            - m_total:          aggregated money supply per day
            """

            def retrieve_per_tx_daily(
                i_day,
                tx,
            ):
                """
                This function retrieves basic blockchain values and aggregates
                them into daily chunks.
                """
                try:
                    if tx.block_height >= Velo.bl_height_max:
                        return

                    txes_daily[i_day].append(tx)
                    txes_count[i_day] += 1
                    txes_fees[i_day]  += tx.fee

                    if tx.output_value <= tx.fee:
                        txes_dust_fees[i_day]   += tx.fee
                        txes_dust_inpval[i_day] += tx.input_value

                    txes_vol[i_day] += tx.output_value

                    val_chouts = 0
                    for out in Velo.heur_select.change(tx):
                        if False == in_max_cluster(out):
                            val_chouts += int(out.value)
                    txes_vol_churn[i_day] += val_chouts

                except IndexError as error:
                    Velo.logger.error(
                        "{}{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}".format(
                            "{}[{}{}/{:03}{}]".format(
                                cs.RES,
                                cs.WHI,
                                self.process_name,
                                Velo.process_cnt-1,
                                cs.RES,
                            ),
                            cs.WHI,
                            "        bl_height      = {}".format(
                                tx.block_height
                            ),
                            "        bl_height_max  = {}".format(
                                Velo.bl_height_max
                            ),
                            "        i_day             = {}".format(i_day),
                            "        day_diff_to_start = {}".format(
                                day_diff_to_start
                            ),
                            "        day_date          = {}".format(day_date),
                            "        date_period_start = {}".format(
                                self.__date_period_start
                            ),
                            "        block_time        = {}".format(
                                tx.block_time
                            ),
                            "        tx.hash           = {}".format(tx.hash),
                            "        is coinbase?      = {}".format(
                                tx.is_coinbase
                            ),
                            error,
                        )
                    )
                    exit(-1)

                return

            #--print process status message-------------------------------------
            Velo.logger.info(
                "{}[{}{}/{:03}{}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBA,
                    self.process_name,
                    Velo.process_cnt-1,
                    cs.RES,
                    "                 ",
                    "{}get_basic_tx_data".format(cs.PRGnBA),
                )
            )

            #--initialize data structures---------------------------------------
            txes_daily       = []            # all transactions of one day------
            index_day        = []            # index list of day ids------------
            txes_count       = []            # daily count of transactions------
            txes_fees        = []            # daily agg. tx fees---------------
            txes_dust_fees   = []            # daily agg. tx dust fees----------
            txes_dust_inpval = []            # daily agg. tx dust input values--
            txes_vol         = []            # daily transaction volume---------
            txes_vol_churn   = []            # daily tx volume selfchurn--------
            m_total          = []            # total money supply up to this day

            # retrieve txes and values per daily grouped txes in process period-
            day_date          = self.__date_period_start
            day_date_next     = day_date
            day_diff_to_start = (
                to_datetime(day_date) -
                to_datetime(Velo.start_date_gen)
            ).days

            for i_day in range(self.__date_period):
                # print a liveliness message if criteria are matched------------
                print_liveliness_message(
                    i_day,
                    "get_basic_tx_data()"
                )

                # initialize daily used data structures-------------------------
                date     = self.__date_period_start + timedelta(i_day)
                date_str = date.strftime("%y/%m/%d")

                txes_daily      .append([])
                index_day       .append(date_str)
                txes_vol        .append(0)
                txes_count      .append(0)
                txes_fees       .append(0)
                txes_dust_fees  .append(0)
                txes_dust_inpval.append(0)
                txes_vol_churn  .append(0)

                # transform date variables--------------------------------------
                # day_date_net_prev = day_date_next
                day_date = day_date_next
                day_date_next += timedelta(days=1)

                # get minimum and maximum bl_height according to actual day--
                bl_height_min = Velo.block_times[
                    Velo.block_times.index >= day_date
                ].iloc[0][0]

                bl_height_max = Velo.block_times[
                    Velo.block_times.index >= day_date_next
                ].iloc[0][0]

                # get list of aggregated coin supply per given block height-----
                m_total.append(Velo.f_m_total_of_bl_height[bl_height_min])

                # retrieve daily txes and values per block in daily blockrange--
                for i_bh in range(bl_height_min, bl_height_max):
                    block = Velo.chain[i_bh]
                    for tx in block:
                        retrieve_per_tx_daily(i_day, tx)

            #--used by subsequent instance level functions----------------------
            self.__txes_daily = txes_daily

            # append results to queue dictionary--------------------------------
            self.__queue_dict["index_day"]      = index_day
            self.__queue_dict["tx_count"]       = txes_count
            self.__queue_dict["tx_fees"]        = txes_fees
            self.__queue_dict["tx_dust_fees"]   = txes_dust_fees
            self.__queue_dict["tx_dust_inpval"] = txes_dust_inpval
            self.__queue_dict["tx_vol"]         = txes_vol
            self.__queue_dict["tx_vol_churn"]   = txes_vol_churn
            self.__queue_dict["m_total"]        = m_total

            #--test and normal returns------------------------------------------
            if Velo.test_level > 0:
                s_txes_vol_churn = str(txes_vol_churn)
                self.__queue_dict["txes_vol_churn"] = s_txes_vol_churn

            if Velo.test_level == 1:
                self.__queue.put([
                    self.stage_id,
                    self.process_id,
                    self.__queue_dict,
                ])
                return True

            return False

        def get_measurements():
            """
            "Coin days destroyed"-approach:-------------------------------------

            We use this weighted average to calculate (1) the summands necessary
            to calculate SDD and (2) the (with the time window transaction
            volume) weighted summands for dormancy.
            Both is calculated first on a tx-wise level (A) and later
            summed up (B). Using the daily sums, finally, using a cum
            sum over a time window function, the two measures can be
            calculated (C).

            Overview: Weighted average used to calculate summands for ... on ...
            (1): ... SDD
            (2): ... (weighed summands) Dormancy
            (A): ... tx-wise/txly level
            (B): ... daychunk level, summed up
            (C): see get_comp_meas_from_summands() in get_df_m_circ()/get_df()

            Note: dsls - Time/Days Since Last Spent
            For non-weighted summands, no 2dim list is necessary, as there is
            no weighting with the tx value over the time window. It is helpful
            to look at the derivation of the equations in our paper.

            "Whole bill"-approach:----------------------------------------------

            Get coin supply in circulation for a given period,
            based on Tx inputs created in earlier periods and new
            minted coins.

            Here: Get circulating supply for each day
            => extract the transactions for each day that satisfy certain
            characteristics. We need tx inputs that where processed and
            generated before the given period. Additionally we need newly
            minted coins that where transacted during the given period.

            "Moved coin"-approach:----------------------------------------------

            Get coin supply in circulation for a given period, based on Tx
            inputs created in earlier periods and new minted coins.
            Inputs converting to change outputs are substracted based on
            either "FIFO" or "LIFO". It is assumed, that inputs are first
            filling up outputs controlled by third party public keys,
            rather than change outputs.

            Here: Get circulating supply for each day

            *) Dust transaction shouldn't be included!
               If all inputs are zero, then the fee and the outputs are
               all zero. Thus, we ignore this transaction since only
               count "time since last spend", which does not occure here.
               Eventually, the weight of this transaction is zero, which
               means that we would not include it in our computation
               anyway.
               fee: output-input
               fee = output => input = 0
               fee > output => input < 0
            """
            def get_timed_input(input, input_value):
                """
                Returns product of input value and time since last spend,
                see definition of coin days destroyed.
                """

                time_sls_input = input.tx.block_time - input.spent_tx.block_time
                secs_sls_input = time_sls_input.total_seconds()
                days_sls_input = secs_sls_input / Velo.secs_per_day

                input_time = days_sls_input * input_value

                return input_time

            def inp_spent_before_bh_or_coinbase(
                inp,
                bl_heights,
                switch_circ_effective,
            ):
                """
                This function represents the condition for the handle_tx_mc
                functions to decide, whether to sum an input or not.
                """

                time_windows     = Velo.time_windows
                time_windows_cnt = len(time_windows)
                inp_spent_index  = [0 for t in range(time_windows_cnt)]
                is_coinbase      = False

                inp_spent_tx_bl_height = inp.spent_tx.block_height

                # if we do not count money in effective circulation, we count---
                # every input
                if switch_circ_effective == False:
                    inp_spent_index = [1 for t in range(time_windows_cnt)]
                    return inp_spent_index

                # check if the tx that spent this input is a coinbase tx--------
                if inp.spent_tx.is_coinbase:
                    for bh_i in range(time_windows_cnt):
                        if inp_spent_tx_bl_height < bl_heights[bh_i] or ( 0 == inp_spent_tx_bl_height and 0 == bl_heights[bh_i] ):
                            inp_spent_index[bh_i] = 2
                        else:
                            inp_spent_index[bh_i] = 3
                    return inp_spent_index

                # if bl_heights[0] <= 0, we discard this input since it cannot--
                # be spent before this block height
                # (bl 0 is start of blockchain)
                if bl_heights[0] <= 0:
                    return inp_spent_index

                # check if the tx that spent this input is older than given-----
                # block height
                inp_spent_tx_bl_height = inp.spent_tx.block_height
                for bh_i in range(time_windows_cnt):
                    if inp_spent_tx_bl_height < bl_heights[bh_i]:
                        inp_spent_index[bh_i] = 1

                return inp_spent_index

            def inp_spent_coinbase(
                tx,
                switch_time=False,
            ):
                """
                """
                time_windows     = Velo.time_windows
                time_windows_cnt = len(time_windows)
                inps             = tx.inputs
                inp_without_fee  = 0
                m_circ_cbs       = 0

                if tx.is_coinbase or tx.input_value == 0:
                    return m_circ_cbs

                else:
                    for inp_i in inps:
                        if inp_i.spent_tx.is_coinbase:
                            inp_without_fee = (
                                inp_i.spent_tx.block.revenue
                                - inp_i.spent_tx.block.fee
                            )

                            if switch_time == True:
                                m_circ_cbs += get_timed_input(
                                    inp_i,
                                    inp_without_fee
                                )
                            else:
                                m_circ_cbs += inp_without_fee

                return m_circ_cbs

            def outs_spent_bl_heights(
                tx,
                bl_heights_post,
                bl_heights,
            ):
                """
                """
                time_windows     = Velo.time_windows
                time_windows_cnt = len(time_windows)
                outs             = tx.outputs
                outs_spent       = [0 for t in range(time_windows_cnt)]

                # drop coinbase txes since they are addresses by----------------
                # inp_spent_coinbase and inp_spent_before_bh_or_coinbase
                if tx.is_coinbase:
                    return outs_spent
                
                # if there are no further days/blocks, we can only subtract 0---
                if bl_heights_post[0] >= Velo.bl_height_max:
                    return outs_spent

                # otherwise, add all outputs that have a spending_tx within the-
                # given window
                for out_i in outs:
                    out_i_spending_tx = out_i.spending_tx

                    # only consider output if it is spent-----------------------
                    if out_i_spending_tx is None:
                        continue

                    bh_out = out_i_spending_tx.block_height

                    # check whether bh_out is in analyzed block range-----------
                    if bh_out >= Velo.bl_height_max:
                        continue

                    # check block heights for each time window------------------
                    for t_w in range(1, time_windows_cnt):
                        bh_tw_post = bl_heights_post[t_w]
                        bh_tw      = bl_heights[t_w]

                        # check whether bh_tw_post is in analyzed block range---
                        if bh_tw_post >= Velo.bl_height_max:
                            continue

                        # check whether bh_out is within window minus one day---
                        if bl_heights_post[0] > bh_out or bh_out >= bh_tw:
                            continue

                        # add if bh_out is within window and before last tw day-
                        # and if its tx is a coinbase tx, since we want to
                        # drop coinbase txos being spent in the last tw day
                        # if bh_out >= bh_tw and tx.is_coinbase:
                        #    continue

                        outs_spent[t_w] += out_i.value

                return outs_spent

            def get_selfchurn(tx):
                """
                This function gets selfchurn outputs of a given transaction.
                """
                val_chouts = 0

                for out in Velo.heur_select.change(tx):
                    if False == in_max_cluster(out):
                        val_chouts += int(out.value)

                return val_chouts

            def handle_tx_m_circ(
                tx,
                bl_heights,
                switch_circ_effective=True,
                switch_wb_bill=True,
                switch_sort=False,
                switch_time=False,
            ):
                """
                Compute and return satoshi days desdroyed (sdd) per tx.
                Whole bill approach: complete agg value of inputs
                Moved-Coin-Approach
                We will do:
                1) For the TX: get the sum of Changeouts,
                   sum of all self-churning outputs
                2) For the TX: the amount of Satoshi *actually sent*,
                   amount of money send to others/sum of self-churning
                   outputs
                3) For the TX: the age-sorted list of inputs
                4) For each input, that is smaller than the accumulated sum
                   of BTC sent to third party, extract it's value and to sum
                   it up later. If only a part of the respective input is
                   needed, it will be corrected. The complete input object
                   is stored as well for later use in filtering out recycled
                   TXOs.
                *) Only those inputs are summed up that either where
                   generated before the respective first_bl_height/period
                   or where spent by a coinbase transaction
                **) Only as much as val_outs_sent_to_others will be summed
                    up.
                """
                #---------------------------------------------------------------
                time_windows     = Velo.time_windows
                time_windows_cnt = len(time_windows)
                m_circ_mc        = [0 for t in range(time_windows_cnt)]
                m_circ_mc_timed  = [0 for t in range(time_windows_cnt)]
                inps             = tx.inputs
                val_outs_break   = 0
                val_outs         = tx.output_value
                bl_heights_loc   = bl_heights

                if tx.input_value == 0 or val_outs == 0 or tx.is_coinbase:
                    return m_circ_mc

                else:
                    # 1)
                    val_outs_sent_to_others = val_outs

                    if switch_wb_bill == True:
                        val_outs_sent_to_others += tx.fee
                    else:
                        val_outs_sent_to_others -= get_selfchurn(tx)

                    # 2)
                    if val_outs_sent_to_others < 0:
                        raise ValueError(
                            "val_outs_sent_to_others must not be less than 0!"
                        )
                    elif val_outs_sent_to_others == 0:
                        return m_circ_mc

                    # 3)
                    if switch_wb_bill == False:
                        inps = sort_together(
                            [
                                inps.age,
                                inps,
                            ],
                            reverse = switch_sort
                        )[1]

                    # 4)
                    for inp_i in inps:
                        val_inp_i = inp_i.value
                        val_outs_break += val_inp_i

                        inp_spent_index = inp_spent_before_bh_or_coinbase(
                            inp_i,
                            bl_heights_loc,
                            switch_circ_effective,
                        )

                        if ( inp_spent_index[0] ):
                            if ( 3 == inp_spent_index[0] ):
                                m_circ_mc[0] += (
                                    inp_i.spent_tx.block.revenue
                                    - inp_i.spent_tx.block.fee
                                )
                            else:
                                m_circ_mc[0] += val_inp_i

                            for t_w in range(1, time_windows_cnt):
                                if ( inp_spent_index[t_w] ):
                                    if ( 3 == inp_spent_index[t_w] ):
                                        m_circ_mc[t_w] += (
                                            inp_i.spent_tx.block.revenue
                                            - inp_i.spent_tx.block.fee
                                        )
                                    else:
                                        m_circ_mc[t_w] += val_inp_i

                            if switch_time == True:
                                if ( 3 == inp_spent_index[0] ):
                                    val_inp_i_timed = get_timed_input(
                                        inp_i,
                                        inp_i.spent_tx.block.revenue - inp_i.spent_tx.block.fee
                                    )
                                else:
                                    val_inp_i_timed = get_timed_input(
                                        inp_i,
                                        val_inp_i,
                                    )

                                m_circ_mc_timed[0] += val_inp_i_timed
                                for t_w in range(1, time_windows_cnt):
                                    if ( inp_spent_index[t_w] ):
                                        m_circ_mc_timed[t_w] += val_inp_i_timed

                            # **)
                            if val_outs_break >= val_outs_sent_to_others:
                                if m_circ_mc[0] >= val_outs_sent_to_others:
                                    m_circ_mc[0] = val_outs_sent_to_others
                                break

                if m_circ_mc[0] < 0:
                    Velo.logger.error(
                        "{}{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}".format(
                            "{}[{}{}/{:03}{}]".format(
                                cs.RES,
                                cs.WHI,
                                self.process_name,
                                Velo.process_cnt-1,
                                cs.RES,
                            ),
                            cs.WHI,
                            "        block_time              = {}".format(
                                tx.block_time
                            ),
                            "        tx.hash                 = {}".format(
                                tx.hash
                            ),
                            "        is coinbase?            = {}".format(
                                tx.is_coinbase
                            ),
                            "        val_outs                = {}".format(
                                val_outs
                            ),
                            "        val_chouts              = {}".format(
                                val_chouts
                            ),
                            "        val_outs_sent_to_others = {}".format(
                                val_outs_sent_to_others
                            ),
                            "        inps_sorted             = {}".format(
                                inps_sorted
                            ),
                            "        val_inps_all            = {}".format(
                                tx.input_value
                            ),
                            "        m_circ_m                = {}".format(
                                m_circ_mc
                            ),
                        )
                    )
                    raise ValueError(
                        "m_circ_m must not be less than 0!"
                        )

                if switch_time == True:
                    return m_circ_mc_timed

                return m_circ_mc

            # print starting message--------------------------------------------
            Velo.logger.info(
                "{}[{}{}/{:03}{}]   {}   {}".format(
                    cs.RES,
                    cs.PRGnBC,
                    self.process_name,
                    Velo.process_cnt-1,
                    cs.RES,
                    "                 ",
                    "{}get measurement results".format(cs.PRGnBC),
                )
            )

            # initialize basic variables/data structures------------------------
            time_windows     = Velo.time_windows
            time_windows_cnt = len(time_windows)
            satoshi_dd_raw   = [[] for t in range(time_windows_cnt)]
            dormancy_raw     = [[] for t in range(time_windows_cnt)]
            m_circ_wh_bill   = [[] for t in range(time_windows_cnt)]
            m_circ_mc_lifo   = [[] for t in range(time_windows_cnt)]
            m_circ_mc_fifo   = [[] for t in range(time_windows_cnt)]
            m_circ_cbs       = []
            m_circ_cbs_timed = []
            outs_spent_btw   = [[] for t in range(time_windows_cnt)]

            # get day_index of first block in self.__txes_daily-----------------
            bh_first        = self.__txes_daily[0][0].block_height
            day_chunk_first = Velo.f_index_day_of_bl_height[bh_first]

            # retrieve data for each daychunk of txes---------------------------
            for daychunk in self.__txes_daily:
                # initialize daily values --------------------------------------
                m_circ_cbs      .append(0)
                m_circ_cbs_timed.append(0)
                for t_w in range(time_windows_cnt):
                    satoshi_dd_raw[t_w].append(0)
                    dormancy_raw[t_w]  .append(0)
                    m_circ_wh_bill[t_w].append(0)
                    m_circ_mc_lifo[t_w].append(0)
                    m_circ_mc_fifo[t_w].append(0)
                    outs_spent_btw[t_w].append(0)

                # if no transactions happened, continue-------------------------
                if daychunk == []:
                    continue

                # initialize first block heights/day index of txes--------------
                bh_tx_pre    = [-1 for t in range(time_windows_cnt)]
                bh_tx        = [-1 for t in range(time_windows_cnt)]
                bh_tx_post   = [-1 for t in range(time_windows_cnt)]
                bh_tx_pre[0] = daychunk[ 0].block_height
                day_index    = Velo.f_index_day_of_bl_height[bh_tx_pre[0]]

                # print some liveliness message---------------------------------
                print_liveliness_message(
                    day_index - day_chunk_first,
                    "get_measurements()"
                )

                # prepare windows values/days and block heights-----------------
                if day_index >= Velo.cnt_days:
                    bh_tx[0]      = Velo.bl_height_max + day_index
                    bh_tx_post[0] = Velo.bl_height_max + day_index + 1 
                else:
                    bh_tx[0]      = Velo.f_bl_height_min_of_index_day[day_index]
                    bh_tx_post[0] = (
                        Velo.f_bl_height_max_of_index_day[day_index] + 1
                    )

                for t_w in range(1, time_windows_cnt):
                    wndw = time_windows[t_w]
                    day_tw_pre  = day_index - wndw + 1
                    day_tw      = day_index + wndw

                    if day_tw_pre >= 0:
                        bh_tx_pre[t_w] = Velo.f_bl_height_min_of_index_day[
                            day_tw_pre
                        ]
                    elif day_tw_pre < 0:
                        bh_tx_pre[t_w] = day_tw_pre

                    if day_tw < Velo.cnt_days-1:
                        bh_tx[t_w]      = (
                            Velo.f_bl_height_min_of_index_day[day_tw]
                        )
                        bh_tx_post[t_w] = (
                            Velo.f_bl_height_max_of_index_day[day_tw] + 1
                        )

                    elif day_tw >= Velo.cnt_days:
                        bh_tx_post[t_w] = Velo.bl_height_max + day_tw + 1
                        bh_tx[t_w]      = Velo.bl_height_max + day_tw 

                # retrieve tx-wise values for money in effective cirulation-----
                for tx in daychunk:
                    # Here, dust transaction shouldn't be included, see *)------
                    if tx.output_value <= tx.fee:
                        continue

                    satoshi_dd_per_tx       = handle_tx_m_circ(
                        tx,
                        bh_tx_pre,
                        switch_circ_effective=False,
                        switch_wb_bill=True,
                        switch_sort=False,
                        switch_time=True,
                    )
                    m_circ_wh_bill_per_tx   = handle_tx_m_circ(
                        tx,
                        bh_tx_pre,
                        switch_circ_effective=True,
                        switch_wb_bill=True,
                        switch_sort=False,
                        switch_time=False,
                    )
                    m_circ_mc_lifo_per_tx   = handle_tx_m_circ(
                        tx,
                        bh_tx_pre,
                        switch_circ_effective=True,
                        switch_wb_bill=False,
                        switch_sort=False,
                        switch_time=False,
                    )
                    m_circ_mc_fifo_per_tx   = handle_tx_m_circ(
                        tx,
                        bh_tx_pre,
                        switch_circ_effective=True,
                        switch_wb_bill=False,
                        switch_sort=True,
                        switch_time=False,
                    )
                    m_circ_cbs_per_tx       = inp_spent_coinbase(
                        tx,
                        False,
                    )
                    m_circ_cbs_timed_per_tx = inp_spent_coinbase(
                        tx,
                        True,
                    )

                    m_circ_cbs[-1]       += m_circ_cbs_per_tx
                    m_circ_cbs_timed[-1] += m_circ_cbs_timed_per_tx

                    # outputs spent within time window are only needed for------
                    # aggregation for window sizes > 1
                    outs_spent_btw_per_tx = [
                        -1 for t in range(time_windows_cnt)
                    ]
                    if time_windows_cnt > 1:
                        outs_spent_btw_per_tx = outs_spent_bl_heights(
                            tx,
                            bh_tx_post,
                            bh_tx
                        )

                    # prepare data structures for windowed values---------------
                    for t_w in range(time_windows_cnt):
                        satoshi_dd_raw[t_w][-1]  += satoshi_dd_per_tx[t_w]
                        dormancy_raw[t_w][-1]    += satoshi_dd_per_tx[t_w]
                        m_circ_wh_bill[t_w][-1]  += m_circ_wh_bill_per_tx[t_w]
                        m_circ_mc_lifo[t_w][-1]  += m_circ_mc_lifo_per_tx[t_w]
                        m_circ_mc_fifo[t_w][-1]  += m_circ_mc_fifo_per_tx[t_w]

                        outs_spent_btw[t_w][-1]  += outs_spent_btw_per_tx[t_w]

            # put results into __queue_dict-------------------------------------
            m_circ_cbs_key       = "m_circ_cbs".format(t_w)
            m_circ_cbs_timed_key = "m_circ_cbs_timed".format(t_w)
            self.__queue_dict[m_circ_cbs_key]       = m_circ_cbs
            self.__queue_dict[m_circ_cbs_timed_key] = m_circ_cbs_timed

            for t_w_i in range(time_windows_cnt):
                t_w = time_windows[t_w_i]
                satoshi_dd_raw_key  = "sdd_raw_{}"        .format(t_w)
                dormancy_raw_key    = "dormancy_raw_{}"   .format(t_w)
                m_circ_wh_bill_key  = "m_circ_wh_bill_{}" .format(t_w)
                m_circ_mc_lifo_key  = "m_circ_mc_lifo_{}" .format(t_w)
                m_circ_mc_fifo_key  = "m_circ_mc_fifo_{}" .format(t_w)

                outs_spent_btw_key  = "outs_spent_btw_{}" .format(t_w)

                self.__queue_dict[satoshi_dd_raw_key] = satoshi_dd_raw[t_w_i]
                self.__queue_dict[dormancy_raw_key]   = dormancy_raw[t_w_i]
                self.__queue_dict[m_circ_wh_bill_key] = m_circ_wh_bill[t_w_i]
                self.__queue_dict[m_circ_mc_lifo_key] = m_circ_mc_lifo[t_w_i]
                self.__queue_dict[m_circ_mc_fifo_key] = m_circ_mc_fifo[t_w_i]
                self.__queue_dict[outs_spent_btw_key] = outs_spent_btw[t_w_i]

            # hande test_level cases--------------------------------------------
            if Velo.test_level == 2:
                self.__queue.put([
                    self.stage_id,
                    self.process_id,
                    self.__queue_dict,
                ])
                return True

            return False

        #-----------------------------------------------------------------------
        if self.stage_id == 0:
            if get_basic_tx_data() == True: return

            self.__queue.put([
                self.stage_id,
                self.process_id,
                self.__queue_evnt_dict
            ])
            self.__queue_evnt_dict = {}

            if get_measurements() == True: return

            while True:
                msg_from_queue = self.__queue_evnt.get()
                msg_stage_id   = msg_from_queue[0]
                msg_process_id = msg_from_queue[1]
                self.__queue_evnt.task_done()

                if msg_stage_id == self.stage_id and msg_process_id == self.process_id:
                    break

            self.stage_id += 1

        if self.stage_id == 1:
            pass

        # put all necessary data to parent process through multiprocess queue---
        Velo.logger.info(
            "{}[{}{}/{:03}{}]   {}   {}".format(
                cs.RES,
                cs.PRGnBE,
                self.process_name,
                Velo.process_cnt-1,
                cs.RES,
                "{}[stage_id     {:2}]".format(
                    cs.WHI,
                    self.stage_id,
                ),
                "{}Sending results".format(cs.PRGnBE),
            )
        )

        self.__queue.put([
            self.stage_id,
            self.process_id,
            self.__queue_dict,
        ])

        Velo.logger.debug(
            "{}[{}{}/{:03}{}]{}   {}   {}".format(
                cs.RES,
                cs.PRGnBE,
                self.process_name,
                Velo.process_cnt-1,
                cs.RES,
                cs.WHI,
                "{}[stage_id     {:2}]".format(
                    cs.WHI,
                    self.stage_id,
                ),
                "{}terminating".format(cs.WHI),
            )
        )

        return

if __name__ == "__main__":
   print("{}Use this file with script.py!{}".format(cs.RED,cs.RES))
   exit(0)
